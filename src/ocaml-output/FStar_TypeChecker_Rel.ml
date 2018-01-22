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
  'Auu____1437 'Auu____1438 .
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob ->
        'Auu____1438 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1438 ->
              'Auu____1437 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1438,'Auu____1437)
                    FStar_TypeChecker_Common.problem
  =
  fun scope  ->
    fun orig  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun reason  ->
                let uu____1475 = next_pid () in
                let uu____1476 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1475;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1476;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let new_problem:
  'Auu____1490 'Auu____1491 .
    FStar_TypeChecker_Env.env ->
      'Auu____1491 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1491 ->
            'Auu____1490 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1491,'Auu____1490)
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
                let uu____1529 = next_pid () in
                let uu____1530 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1529;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1530;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = [reason];
                  FStar_TypeChecker_Common.loc = loc;
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let problem_using_guard:
  'Auu____1543 'Auu____1544 .
    FStar_TypeChecker_Common.prob ->
      'Auu____1544 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1544 ->
            'Auu____1543 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____1544,'Auu____1543) FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____1577 = next_pid () in
              {
                FStar_TypeChecker_Common.pid = uu____1577;
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
  'Auu____1583 .
    worklist ->
      ('Auu____1583,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
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
        let uu____1633 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1633
        then
          let uu____1634 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1635 = prob_to_string env d in
          let uu____1636 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1634 uu____1635 uu____1636 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1642 -> failwith "impossible" in
           let uu____1643 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1657 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1658 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1657, uu____1658)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1664 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1665 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1664, uu____1665) in
           match uu____1643 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___96_1681  ->
            match uu___96_1681 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1693 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1695),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___97_1715  ->
           match uu___97_1715 with
           | UNIV uu____1718 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1724),t) ->
               let uu____1730 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1730
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
        (fun uu___98_1750  ->
           match uu___98_1750 with
           | UNIV (u',t) ->
               let uu____1755 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1755
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1759 -> FStar_Pervasives_Native.None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1766 =
        let uu____1767 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____1767 in
      FStar_Syntax_Subst.compress uu____1766
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1774 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1774
let norm_arg:
  'Auu____1778 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____1778) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1778)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____1799 = sn env (FStar_Pervasives_Native.fst t) in
      (uu____1799, (FStar_Pervasives_Native.snd t))
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
           (fun uu____1830  ->
              match uu____1830 with
              | (x,imp) ->
                  let uu____1841 =
                    let uu___122_1842 = x in
                    let uu____1843 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___122_1842.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___122_1842.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1843
                    } in
                  (uu____1841, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1858 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1858
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1862 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1862
        | uu____1865 -> u2 in
      let uu____1866 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1866
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
                (let uu____1978 = norm_refinement env t12 in
                 match uu____1978 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____1995;
                     FStar_Syntax_Syntax.vars = uu____1996;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2022 =
                       let uu____2023 = FStar_Syntax_Print.term_to_string tt in
                       let uu____2024 = FStar_Syntax_Print.tag_of_term tt in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2023 uu____2024 in
                     failwith uu____2022)
          | FStar_Syntax_Syntax.Tm_uinst uu____2039 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____2076 =
                   let uu____2077 = FStar_Syntax_Subst.compress t1' in
                   uu____2077.FStar_Syntax_Syntax.n in
                 match uu____2076 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2094 -> aux true t1'
                 | uu____2101 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2116 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____2147 =
                   let uu____2148 = FStar_Syntax_Subst.compress t1' in
                   uu____2148.FStar_Syntax_Syntax.n in
                 match uu____2147 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2165 -> aux true t1'
                 | uu____2172 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2187 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____2232 =
                   let uu____2233 = FStar_Syntax_Subst.compress t1' in
                   uu____2233.FStar_Syntax_Syntax.n in
                 match uu____2232 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2250 -> aux true t1'
                 | uu____2257 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2272 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2287 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2302 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2317 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2332 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2359 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2390 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2421 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____2448 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____2485 ->
              let uu____2492 =
                let uu____2493 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2494 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2493 uu____2494 in
              failwith uu____2492
          | FStar_Syntax_Syntax.Tm_ascribed uu____2509 ->
              let uu____2536 =
                let uu____2537 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2538 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2537 uu____2538 in
              failwith uu____2536
          | FStar_Syntax_Syntax.Tm_delayed uu____2553 ->
              let uu____2578 =
                let uu____2579 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2580 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2579 uu____2580 in
              failwith uu____2578
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____2595 =
                let uu____2596 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2597 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2596 uu____2597 in
              failwith uu____2595 in
        let uu____2612 = whnf env t1 in aux false uu____2612
let base_and_refinement:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t
let normalize_refinement:
  'Auu____2634 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____2634 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
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
      let uu____2657 = base_and_refinement env t in
      FStar_All.pipe_right uu____2657 FStar_Pervasives_Native.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____2691 = FStar_Syntax_Syntax.null_bv t in
    (uu____2691, FStar_Syntax_Util.t_true)
let as_refinement:
  'Auu____2697 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____2697 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____2718 = base_and_refinement_maybe_delta delta1 env t in
          match uu____2718 with
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
  fun uu____2797  ->
    match uu____2797 with
    | (t_base,refopt) ->
        let uu____2824 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
        (match uu____2824 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2856 =
      let uu____2859 =
        let uu____2862 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2885  ->
                  match uu____2885 with | (uu____2892,uu____2893,x) -> x)) in
        FStar_List.append wl.attempting uu____2862 in
      FStar_List.map (wl_prob_to_string wl) uu____2859 in
    FStar_All.pipe_right uu____2856 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2906 =
          let uu____2919 =
            let uu____2920 = FStar_Syntax_Subst.compress k in
            uu____2920.FStar_Syntax_Syntax.n in
          match uu____2919 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2973 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2973)
              else
                (let uu____2987 = FStar_Syntax_Util.abs_formals t in
                 match uu____2987 with
                 | (ys',t1,uu____3010) ->
                     let uu____3015 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____3015))
          | uu____3056 ->
              let uu____3057 =
                let uu____3068 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____3068) in
              ((ys, t), uu____3057) in
        match uu____2906 with
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
                 let uu____3117 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____3117 c in
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
            let uu____3145 = p_guard prob in
            match uu____3145 with
            | (uu____3150,uv) ->
                ((let uu____3153 =
                    let uu____3154 = FStar_Syntax_Subst.compress uv in
                    uu____3154.FStar_Syntax_Syntax.n in
                  match uu____3153 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____3186 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____3186
                        then
                          let uu____3187 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____3188 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____3189 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3187
                            uu____3188 uu____3189
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____3191 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___123_3194 = wl in
                  {
                    attempting = (uu___123_3194.attempting);
                    wl_deferred = (uu___123_3194.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___123_3194.defer_ok);
                    smt_ok = (uu___123_3194.smt_ok);
                    tcenv = (uu___123_3194.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3209 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____3209
         then
           let uu____3210 = FStar_Util.string_of_int pid in
           let uu____3211 =
             let uu____3212 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____3212 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3210 uu____3211
         else ());
        commit sol;
        (let uu___124_3219 = wl in
         {
           attempting = (uu___124_3219.attempting);
           wl_deferred = (uu___124_3219.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___124_3219.defer_ok);
           smt_ok = (uu___124_3219.smt_ok);
           tcenv = (uu___124_3219.tcenv)
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
            | (uu____3257,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3269 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____3269 in
          (let uu____3275 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____3275
           then
             let uu____3276 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____3277 =
               let uu____3278 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____3278 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____3276 uu____3277
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
        let uu____3310 =
          let uu____3317 = FStar_Syntax_Free.uvars t in
          FStar_All.pipe_right uu____3317 FStar_Util.set_elements in
        FStar_All.pipe_right uu____3310
          (FStar_Util.for_some
             (fun uu____3353  ->
                match uu____3353 with
                | (uv,uu____3359) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
let occurs_check:
  'Auu____3366 'Auu____3367 .
    'Auu____3367 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3366)
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
            let uu____3399 = occurs wl uk t in Prims.op_Negation uu____3399 in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3406 =
                 let uu____3407 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk) in
                 let uu____3408 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3407 uu____3408 in
               FStar_Pervasives_Native.Some uu____3406) in
          (occurs_ok, msg)
let occurs_and_freevars_check:
  'Auu____3418 'Auu____3419 .
    'Auu____3419 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3418)
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
            let uu____3473 = occurs_check env wl uk t in
            match uu____3473 with
            | (occurs_ok,msg) ->
                let uu____3504 = FStar_Util.set_is_subset_of fvs_t fvs in
                (occurs_ok, uu____3504, (msg, fvs, fvs_t))
let intersect_vars:
  'Auu____3527 'Auu____3528 .
    (FStar_Syntax_Syntax.bv,'Auu____3528) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3527) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3527) FStar_Pervasives_Native.tuple2
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
      let uu____3612 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3666  ->
                fun uu____3667  ->
                  match (uu____3666, uu____3667) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____3748 =
                        let uu____3749 = FStar_Util.set_mem x v1_set in
                        FStar_All.pipe_left Prims.op_Negation uu____3749 in
                      if uu____3748
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                         let uu____3774 =
                           FStar_Util.set_is_subset_of fvs isect_set in
                         if uu____3774
                         then
                           let uu____3787 = FStar_Util.set_add x isect_set in
                           (((x, imp) :: isect), uu____3787)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names)) in
      match uu____3612 with | (isect,uu____3828) -> FStar_List.rev isect
let binders_eq:
  'Auu____3853 'Auu____3854 .
    (FStar_Syntax_Syntax.bv,'Auu____3854) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3853) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____3909  ->
              fun uu____3910  ->
                match (uu____3909, uu____3910) with
                | ((a,uu____3928),(b,uu____3930)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt:
  'Auu____3944 'Auu____3945 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____3945) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____3944)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____3944)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____3996 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4010  ->
                      match uu____4010 with
                      | (b,uu____4016) -> FStar_Syntax_Syntax.bv_eq a b)) in
            if uu____3996
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4032 -> FStar_Pervasives_Native.None
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
            let uu____4105 = pat_var_opt env seen hd1 in
            (match uu____4105 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4119 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____4119
                   then
                     let uu____4120 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4120
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4138 =
      let uu____4139 = FStar_Syntax_Subst.compress t in
      uu____4139.FStar_Syntax_Syntax.n in
    match uu____4138 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4142 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4159;
           FStar_Syntax_Syntax.pos = uu____4160;
           FStar_Syntax_Syntax.vars = uu____4161;_},uu____4162)
        -> true
    | uu____4199 -> false
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
           FStar_Syntax_Syntax.pos = uu____4323;
           FStar_Syntax_Syntax.vars = uu____4324;_},args)
        -> (t, uv, k, args)
    | uu____4392 -> failwith "Not a flex-uvar"
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
      let uu____4469 = destruct_flex_t t in
      match uu____4469 with
      | (t1,uv,k,args) ->
          let uu____4584 = pat_vars env [] args in
          (match uu____4584 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4682 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch[@@deriving show]
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____4763 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____4798 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____4802 -> false
let head_match: match_result -> match_result =
  fun uu___99_4805  ->
    match uu___99_4805 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____4820 -> HeadMatch
let and_match: match_result -> (Prims.unit -> match_result) -> match_result =
  fun m1  ->
    fun m2  ->
      match m1 with
      | MisMatch (i,j) -> MisMatch (i, j)
      | HeadMatch  ->
          let uu____4846 = m2 () in
          (match uu____4846 with
           | MisMatch (i,j) -> MisMatch (i, j)
           | uu____4861 -> HeadMatch)
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____4870 ->
          let uu____4871 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____4871 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____4882 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____4901 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____4910 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____4937 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____4938 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____4939 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____4956 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____4969 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____4993) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4999,uu____5000) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5042) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5063;
             FStar_Syntax_Syntax.index = uu____5064;
             FStar_Syntax_Syntax.sort = t2;_},uu____5066)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5073 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5074 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5075 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5088 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5106 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____5106
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
            let uu____5133 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____5133
            then FullMatch
            else
              (let uu____5135 =
                 let uu____5144 =
                   let uu____5147 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____5147 in
                 let uu____5148 =
                   let uu____5151 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____5151 in
                 (uu____5144, uu____5148) in
               MisMatch uu____5135)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5157),FStar_Syntax_Syntax.Tm_uinst (g,uu____5159)) ->
            let uu____5168 = head_matches env f g in
            FStar_All.pipe_right uu____5168 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5171 = FStar_Const.eq_const c d in
            if uu____5171
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5178),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5180)) ->
            let uu____5229 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____5229
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5236),FStar_Syntax_Syntax.Tm_refine (y,uu____5238)) ->
            let uu____5247 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5247 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5249),uu____5250) ->
            let uu____5255 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____5255 head_match
        | (uu____5256,FStar_Syntax_Syntax.Tm_refine (x,uu____5258)) ->
            let uu____5263 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5263 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5264,FStar_Syntax_Syntax.Tm_type
           uu____5265) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5266,FStar_Syntax_Syntax.Tm_arrow uu____5267) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            if (FStar_List.length bs1) = (FStar_List.length bs2)
            then
              let uu____5396 =
                let uu____5397 = FStar_List.zip bs1 bs2 in
                let uu____5432 = head_matches env t12 t22 in
                FStar_List.fold_right
                  (fun uu____5441  ->
                     fun a  ->
                       match uu____5441 with
                       | (b1,b2) ->
                           and_match a
                             (fun uu____5450  -> branch_matches env b1 b2))
                  uu____5397 uu____5432 in
              FStar_All.pipe_right uu____5396 head_match
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5457),FStar_Syntax_Syntax.Tm_app (head',uu____5459))
            ->
            let uu____5500 = head_matches env head1 head' in
            FStar_All.pipe_right uu____5500 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5502),uu____5503) ->
            let uu____5524 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____5524 head_match
        | (uu____5525,FStar_Syntax_Syntax.Tm_app (head1,uu____5527)) ->
            let uu____5548 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____5548 head_match
        | uu____5549 ->
            let uu____5554 =
              let uu____5563 = delta_depth_of_term env t11 in
              let uu____5566 = delta_depth_of_term env t21 in
              (uu____5563, uu____5566) in
            MisMatch uu____5554
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
          | (uu____5618,uu____5619) -> false in
        let uu____5628 = b1 in
        match uu____5628 with
        | (p1,w1,t1) ->
            let uu____5648 = b2 in
            (match uu____5648 with
             | (p2,w2,t2) ->
                 let uu____5668 = FStar_Syntax_Syntax.eq_pat p1 p2 in
                 if uu____5668
                 then
                   let uu____5669 =
                     (let uu____5672 = FStar_Syntax_Util.eq_tm t1 t2 in
                      uu____5672 = FStar_Syntax_Util.Equal) &&
                       (related_by
                          (fun t11  ->
                             fun t21  ->
                               let uu____5681 =
                                 FStar_Syntax_Util.eq_tm t11 t21 in
                               uu____5681 = FStar_Syntax_Util.Equal) w1 w2) in
                   (if uu____5669
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
  'Auu____5697 .
    FStar_TypeChecker_Env.env ->
      'Auu____5697 ->
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
            let uu____5730 = FStar_Syntax_Util.head_and_args t in
            match uu____5730 with
            | (head1,uu____5748) ->
                let uu____5769 =
                  let uu____5770 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5770.FStar_Syntax_Syntax.n in
                (match uu____5769 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5776 =
                       let uu____5777 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_All.pipe_right uu____5777 FStar_Option.isSome in
                     if uu____5776
                     then
                       let uu____5796 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t in
                       FStar_All.pipe_right uu____5796
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                     else FStar_Pervasives_Native.None
                 | uu____5800 -> FStar_Pervasives_Native.None) in
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
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5903)
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5921 =
                     let uu____5930 = maybe_inline t11 in
                     let uu____5933 = maybe_inline t21 in
                     (uu____5930, uu____5933) in
                   match uu____5921 with
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
                (uu____5970,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5988 =
                     let uu____5997 = maybe_inline t11 in
                     let uu____6000 = maybe_inline t21 in
                     (uu____5997, uu____6000) in
                   match uu____5988 with
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
                let uu____6043 = FStar_TypeChecker_Common.decr_delta_depth d1 in
                (match uu____6043 with
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
                let uu____6066 =
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
                (match uu____6066 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6090 -> fail r
            | uu____6099 -> success n_delta r t11 t21 in
          aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp[@@deriving show]
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____6132 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____6168 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list[@@deriving show]
let tc_to_string: tc -> Prims.string =
  fun uu___100_6180  ->
    match uu___100_6180 with
    | T (t,uu____6182) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6198 = FStar_Syntax_Util.type_u () in
      match uu____6198 with
      | (t,uu____6204) ->
          let uu____6205 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____6205
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____6216 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____6216 FStar_Pervasives_Native.fst
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
        let uu____6280 = head_matches env t1 t' in
        match uu____6280 with
        | MisMatch uu____6281 -> false
        | uu____6290 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6386,imp),T (t2,uu____6389)) -> (t2, imp)
                     | uu____6408 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6475  ->
                    match uu____6475 with
                    | (t2,uu____6489) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6532 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6532 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6607))::tcs2) ->
                       aux
                         (((let uu___125_6642 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___125_6642.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___125_6642.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6660 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___101_6713 =
                 match uu___101_6713 with
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
               let uu____6830 = decompose1 [] bs1 in
               (rebuild, matches, uu____6830))
      | uu____6879 ->
          let rebuild uu___102_6885 =
            match uu___102_6885 with
            | [] -> t1
            | uu____6888 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___103_6919  ->
    match uu___103_6919 with
    | T (t,uu____6921) -> t
    | uu____6930 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___104_6933  ->
    match uu___104_6933 with
    | T (t,uu____6935) -> FStar_Syntax_Syntax.as_arg t
    | uu____6944 -> failwith "Impossible"
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
              | (uu____7050,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____7075 = new_uvar r scope1 k in
                  (match uu____7075 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7093 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____7110 =
                         let uu____7111 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____7111 in
                       ((T (gi_xs, mk_kind)), uu____7110))
              | (uu____7124,uu____7125,C uu____7126) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7273 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7290;
                         FStar_Syntax_Syntax.vars = uu____7291;_})
                        ->
                        let uu____7314 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7314 with
                         | (T (gi_xs,uu____7338),prob) ->
                             let uu____7348 =
                               let uu____7349 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____7349 in
                             (uu____7348, [prob])
                         | uu____7352 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7367;
                         FStar_Syntax_Syntax.vars = uu____7368;_})
                        ->
                        let uu____7391 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7391 with
                         | (T (gi_xs,uu____7415),prob) ->
                             let uu____7425 =
                               let uu____7426 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____7426 in
                             (uu____7425, [prob])
                         | uu____7429 -> failwith "impossible")
                    | (uu____7440,uu____7441,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7443;
                         FStar_Syntax_Syntax.vars = uu____7444;_})
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
                        let uu____7575 =
                          let uu____7584 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____7584 FStar_List.unzip in
                        (match uu____7575 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7638 =
                                 let uu____7639 =
                                   let uu____7642 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____7642 un_T in
                                 let uu____7643 =
                                   let uu____7652 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____7652
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7639;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7643;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7638 in
                             ((C gi_xs), sub_probs))
                    | uu____7661 ->
                        let uu____7674 = sub_prob scope1 args q in
                        (match uu____7674 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____7273 with
                   | (tc,probs) ->
                       let uu____7705 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7768,uu____7769),T
                            (t,uu____7771)) ->
                             let b1 =
                               ((let uu___126_7808 = b in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___126_7808.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___126_7808.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp) in
                             let uu____7809 =
                               let uu____7816 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1 in
                               uu____7816 :: args in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7809)
                         | uu____7851 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____7705 with
                        | (bopt,scope2,args1) ->
                            let uu____7935 = aux scope2 args1 qs2 in
                            (match uu____7935 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____7972 =
                                         let uu____7975 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____7975 in
                                       FStar_Syntax_Util.mk_conj_l uu____7972
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____7998 =
                                         let uu____8001 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____8002 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____8001 :: uu____8002 in
                                       FStar_Syntax_Util.mk_conj_l uu____7998 in
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
  'Auu____8070 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8070)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8070)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___127_8091 = p in
      let uu____8096 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____8097 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___127_8091.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8096;
        FStar_TypeChecker_Common.relation =
          (uu___127_8091.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8097;
        FStar_TypeChecker_Common.element =
          (uu___127_8091.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___127_8091.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___127_8091.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___127_8091.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___127_8091.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___127_8091.FStar_TypeChecker_Common.rank)
      }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8109 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____8109
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____8118 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8138 = compress_prob wl pr in
        FStar_All.pipe_right uu____8138 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8148 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____8148 with
           | (lh,uu____8168) ->
               let uu____8189 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____8189 with
                | (rh,uu____8209) ->
                    let uu____8230 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8247,FStar_Syntax_Syntax.Tm_uvar uu____8248)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8285,uu____8286)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8307,FStar_Syntax_Syntax.Tm_uvar uu____8308)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8329,uu____8330)
                          ->
                          let uu____8347 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____8347 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8396 ->
                                    let rank =
                                      let uu____8404 = is_top_level_prob prob in
                                      if uu____8404
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____8406 =
                                      let uu___128_8411 = tp in
                                      let uu____8416 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___128_8411.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___128_8411.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___128_8411.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8416;
                                        FStar_TypeChecker_Common.element =
                                          (uu___128_8411.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___128_8411.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___128_8411.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___128_8411.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___128_8411.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___128_8411.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____8406)))
                      | (uu____8427,FStar_Syntax_Syntax.Tm_uvar uu____8428)
                          ->
                          let uu____8445 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____8445 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8494 ->
                                    let uu____8501 =
                                      let uu___129_8508 = tp in
                                      let uu____8513 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___129_8508.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8513;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___129_8508.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___129_8508.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___129_8508.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___129_8508.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___129_8508.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___129_8508.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___129_8508.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___129_8508.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____8501)))
                      | (uu____8530,uu____8531) -> (rigid_rigid, tp) in
                    (match uu____8230 with
                     | (rank,tp1) ->
                         let uu____8550 =
                           FStar_All.pipe_right
                             (let uu___130_8556 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___130_8556.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___130_8556.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___130_8556.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___130_8556.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___130_8556.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___130_8556.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___130_8556.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___130_8556.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___130_8556.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50) in
                         (rank, uu____8550))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8566 =
            FStar_All.pipe_right
              (let uu___131_8572 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___131_8572.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___131_8572.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___131_8572.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___131_8572.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___131_8572.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___131_8572.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___131_8572.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___131_8572.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___131_8572.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51) in
          (rigid_rigid, uu____8566)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____8627 probs =
      match uu____8627 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8680 = rank wl hd1 in
               (match uu____8680 with
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
    match projectee with | UDeferred _0 -> true | uu____8787 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8799 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8811 -> false
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
                        let uu____8851 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____8851 with
                        | (k,uu____8857) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8867 -> false)))
            | uu____8868 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____8919 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____8919 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____8922 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____8932 =
                     let uu____8933 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____8934 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____8933
                       uu____8934 in
                   UFailed uu____8932)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8954 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8954 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8976 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8976 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____8979 ->
                let uu____8984 =
                  let uu____8985 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____8986 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8985
                    uu____8986 msg in
                UFailed uu____8984 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8987,uu____8988) ->
              let uu____8989 =
                let uu____8990 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8991 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8990 uu____8991 in
              failwith uu____8989
          | (FStar_Syntax_Syntax.U_unknown ,uu____8992) ->
              let uu____8993 =
                let uu____8994 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8995 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8994 uu____8995 in
              failwith uu____8993
          | (uu____8996,FStar_Syntax_Syntax.U_bvar uu____8997) ->
              let uu____8998 =
                let uu____8999 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9000 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8999 uu____9000 in
              failwith uu____8998
          | (uu____9001,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9002 =
                let uu____9003 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9004 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9003 uu____9004 in
              failwith uu____9002
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9028 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____9028
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____9050 = occurs_univ v1 u3 in
              if uu____9050
              then
                let uu____9051 =
                  let uu____9052 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9053 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9052 uu____9053 in
                try_umax_components u11 u21 uu____9051
              else
                (let uu____9055 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9055)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____9075 = occurs_univ v1 u3 in
              if uu____9075
              then
                let uu____9076 =
                  let uu____9077 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9078 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9077 uu____9078 in
                try_umax_components u11 u21 uu____9076
              else
                (let uu____9080 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9080)
          | (FStar_Syntax_Syntax.U_max uu____9089,uu____9090) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9096 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9096
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9098,FStar_Syntax_Syntax.U_max uu____9099) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9105 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9105
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9107,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9108,FStar_Syntax_Syntax.U_name
             uu____9109) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9110) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9111) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9112,FStar_Syntax_Syntax.U_succ
             uu____9113) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9114,FStar_Syntax_Syntax.U_zero
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
      let uu____9200 = bc1 in
      match uu____9200 with
      | (bs1,mk_cod1) ->
          let uu____9241 = bc2 in
          (match uu____9241 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____9311 = FStar_Util.first_N n1 bs in
                 match uu____9311 with
                 | (bs3,rest) ->
                     let uu____9336 = mk_cod rest in (bs3, uu____9336) in
               let l1 = FStar_List.length bs1 in
               let l2 = FStar_List.length bs2 in
               if l1 = l2
               then
                 let uu____9365 =
                   let uu____9372 = mk_cod1 [] in (bs1, uu____9372) in
                 let uu____9375 =
                   let uu____9382 = mk_cod2 [] in (bs2, uu____9382) in
                 (uu____9365, uu____9375)
               else
                 if l1 > l2
                 then
                   (let uu____9424 = curry l2 bs1 mk_cod1 in
                    let uu____9437 =
                      let uu____9444 = mk_cod2 [] in (bs2, uu____9444) in
                    (uu____9424, uu____9437))
                 else
                   (let uu____9460 =
                      let uu____9467 = mk_cod1 [] in (bs1, uu____9467) in
                    let uu____9470 = curry l1 bs2 mk_cod2 in
                    (uu____9460, uu____9470)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____9591 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9591
       then
         let uu____9592 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9592
       else ());
      (let uu____9594 = next_prob probs in
       match uu____9594 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___132_9615 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___132_9615.wl_deferred);
               ctr = (uu___132_9615.ctr);
               defer_ok = (uu___132_9615.defer_ok);
               smt_ok = (uu___132_9615.smt_ok);
               tcenv = (uu___132_9615.tcenv)
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
                  let uu____9626 = solve_flex_rigid_join env tp probs1 in
                  (match uu____9626 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9631 = solve_rigid_flex_meet env tp probs1 in
                     match uu____9631 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9636,uu____9637) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9654 ->
                let uu____9663 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9722  ->
                          match uu____9722 with
                          | (c,uu____9730,uu____9731) -> c < probs.ctr)) in
                (match uu____9663 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9772 =
                            FStar_List.map
                              (fun uu____9787  ->
                                 match uu____9787 with
                                 | (uu____9798,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____9772
                      | uu____9801 ->
                          let uu____9810 =
                            let uu___133_9811 = probs in
                            let uu____9812 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9833  ->
                                      match uu____9833 with
                                      | (uu____9840,uu____9841,y) -> y)) in
                            {
                              attempting = uu____9812;
                              wl_deferred = rest;
                              ctr = (uu___133_9811.ctr);
                              defer_ok = (uu___133_9811.defer_ok);
                              smt_ok = (uu___133_9811.smt_ok);
                              tcenv = (uu___133_9811.tcenv)
                            } in
                          solve env uu____9810))))
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
            let uu____9848 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____9848 with
            | USolved wl1 ->
                let uu____9850 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____9850
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
                  let uu____9896 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____9896 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9899 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9911;
                  FStar_Syntax_Syntax.vars = uu____9912;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9915;
                  FStar_Syntax_Syntax.vars = uu____9916;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9930,uu____9931) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9938,FStar_Syntax_Syntax.Tm_uinst uu____9939) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9946 -> USolved wl
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
            ((let uu____9956 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____9956
              then
                let uu____9957 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____9957 msg
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
        (let uu____9966 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____9966
         then
           let uu____9967 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____9967
         else ());
        (let uu____9969 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____9969 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____10031 = head_matches_delta env () t1 t2 in
               match uu____10031 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____10072 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____10121 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10136 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____10137 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____10136, uu____10137)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10142 =
                                FStar_Syntax_Subst.compress t1 in
                              let uu____10143 =
                                FStar_Syntax_Subst.compress t2 in
                              (uu____10142, uu____10143) in
                        (match uu____10121 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____10169 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____10169 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____10200 =
                                    let uu____10209 =
                                      let uu____10212 =
                                        let uu____10215 =
                                          let uu____10216 =
                                            let uu____10223 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____10223) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____10216 in
                                        FStar_Syntax_Syntax.mk uu____10215 in
                                      uu____10212
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____10231 =
                                      let uu____10234 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____10234] in
                                    (uu____10209, uu____10231) in
                                  FStar_Pervasives_Native.Some uu____10200
                              | (uu____10247,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10249)) ->
                                  let uu____10254 =
                                    let uu____10261 =
                                      let uu____10264 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____10264] in
                                    (t11, uu____10261) in
                                  FStar_Pervasives_Native.Some uu____10254
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10274),uu____10275) ->
                                  let uu____10280 =
                                    let uu____10287 =
                                      let uu____10290 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____10290] in
                                    (t21, uu____10287) in
                                  FStar_Pervasives_Native.Some uu____10280
                              | uu____10299 ->
                                  let uu____10304 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____10304 with
                                   | (head1,uu____10328) ->
                                       let uu____10349 =
                                         let uu____10350 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____10350.FStar_Syntax_Syntax.n in
                                       (match uu____10349 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10361;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10363;_}
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
                                        | uu____10370 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10383) ->
                  let uu____10408 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___105_10434  ->
                            match uu___105_10434 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10441 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____10441 with
                                      | (u',uu____10457) ->
                                          let uu____10478 =
                                            let uu____10479 = whnf env u' in
                                            uu____10479.FStar_Syntax_Syntax.n in
                                          (match uu____10478 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10483) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10508 -> false))
                                 | uu____10509 -> false)
                            | uu____10512 -> false)) in
                  (match uu____10408 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10546 tps =
                         match uu____10546 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10594 =
                                    let uu____10603 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____10603 in
                                  (match uu____10594 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10638 -> FStar_Pervasives_Native.None) in
                       let uu____10647 =
                         let uu____10656 =
                           let uu____10663 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____10663, []) in
                         make_lower_bound uu____10656 lower_bounds in
                       (match uu____10647 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10675 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10675
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
                            ((let uu____10695 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10695
                              then
                                let wl' =
                                  let uu___134_10697 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___134_10697.wl_deferred);
                                    ctr = (uu___134_10697.ctr);
                                    defer_ok = (uu___134_10697.defer_ok);
                                    smt_ok = (uu___134_10697.smt_ok);
                                    tcenv = (uu___134_10697.tcenv)
                                  } in
                                let uu____10698 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10698
                              else ());
                             (let uu____10700 =
                                solve_t env eq_prob
                                  (let uu___135_10702 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___135_10702.wl_deferred);
                                     ctr = (uu___135_10702.ctr);
                                     defer_ok = (uu___135_10702.defer_ok);
                                     smt_ok = (uu___135_10702.smt_ok);
                                     tcenv = (uu___135_10702.tcenv)
                                   }) in
                              match uu____10700 with
                              | Success uu____10705 ->
                                  let wl1 =
                                    let uu___136_10707 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___136_10707.wl_deferred);
                                      ctr = (uu___136_10707.ctr);
                                      defer_ok = (uu___136_10707.defer_ok);
                                      smt_ok = (uu___136_10707.smt_ok);
                                      tcenv = (uu___136_10707.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____10709 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10714 -> FStar_Pervasives_Native.None))))
              | uu____10715 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10724 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10724
         then
           let uu____10725 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10725
         else ());
        (let uu____10727 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____10727 with
         | (u,args) ->
             let uu____10766 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____10766 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____10807 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____10807 with
                    | (h1,args1) ->
                        let uu____10848 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____10848 with
                         | (h2,uu____10868) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____10895 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____10895
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____10913 =
                                          let uu____10916 =
                                            let uu____10917 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____10917 in
                                          [uu____10916] in
                                        FStar_Pervasives_Native.Some
                                          uu____10913))
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
                                       (let uu____10950 =
                                          let uu____10953 =
                                            let uu____10954 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____10954 in
                                          [uu____10953] in
                                        FStar_Pervasives_Native.Some
                                          uu____10950))
                                  else FStar_Pervasives_Native.None
                              | uu____10968 -> FStar_Pervasives_Native.None)) in
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
                             let uu____11058 =
                               let uu____11067 =
                                 let uu____11070 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____11070 in
                               (uu____11067, m1) in
                             FStar_Pervasives_Native.Some uu____11058)
                    | (uu____11083,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____11085)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____11133),uu____11134) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____11181 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11234) ->
                       let uu____11259 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___106_11285  ->
                                 match uu___106_11285 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____11292 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____11292 with
                                           | (u',uu____11308) ->
                                               let uu____11329 =
                                                 let uu____11330 =
                                                   whnf env u' in
                                                 uu____11330.FStar_Syntax_Syntax.n in
                                               (match uu____11329 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11334) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11359 -> false))
                                      | uu____11360 -> false)
                                 | uu____11363 -> false)) in
                       (match uu____11259 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11401 tps =
                              match uu____11401 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11463 =
                                         let uu____11474 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____11474 in
                                       (match uu____11463 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11525 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____11536 =
                              let uu____11547 =
                                let uu____11556 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____11556, []) in
                              make_upper_bound uu____11547 upper_bounds in
                            (match uu____11536 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11570 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11570
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
                                 ((let uu____11596 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11596
                                   then
                                     let wl' =
                                       let uu___137_11598 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___137_11598.wl_deferred);
                                         ctr = (uu___137_11598.ctr);
                                         defer_ok = (uu___137_11598.defer_ok);
                                         smt_ok = (uu___137_11598.smt_ok);
                                         tcenv = (uu___137_11598.tcenv)
                                       } in
                                     let uu____11599 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11599
                                   else ());
                                  (let uu____11601 =
                                     solve_t env eq_prob
                                       (let uu___138_11603 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___138_11603.wl_deferred);
                                          ctr = (uu___138_11603.ctr);
                                          defer_ok =
                                            (uu___138_11603.defer_ok);
                                          smt_ok = (uu___138_11603.smt_ok);
                                          tcenv = (uu___138_11603.tcenv)
                                        }) in
                                   match uu____11601 with
                                   | Success uu____11606 ->
                                       let wl1 =
                                         let uu___139_11608 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___139_11608.wl_deferred);
                                           ctr = (uu___139_11608.ctr);
                                           defer_ok =
                                             (uu___139_11608.defer_ok);
                                           smt_ok = (uu___139_11608.smt_ok);
                                           tcenv = (uu___139_11608.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____11610 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11615 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11616 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____11691 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____11691
                      then
                        let uu____11692 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11692
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___140_11746 = hd1 in
                      let uu____11747 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___140_11746.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___140_11746.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11747
                      } in
                    let hd21 =
                      let uu___141_11751 = hd2 in
                      let uu____11752 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___141_11751.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___141_11751.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11752
                      } in
                    let prob =
                      let uu____11756 =
                        let uu____11761 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11761 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____11756 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____11772 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11772 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____11776 =
                      aux (FStar_List.append scope [(hd12, imp)]) env2 subst2
                        xs1 ys1 in
                    (match uu____11776 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11814 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____11819 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____11814 uu____11819 in
                         ((let uu____11829 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____11829
                           then
                             let uu____11830 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____11831 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11830 uu____11831
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11854 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____11864 = aux scope env [] bs1 bs2 in
              match uu____11864 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____11888 = compress_tprob wl problem in
        solve_t' env uu____11888 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____11921 = head_matches_delta env1 wl1 t1 t2 in
          match uu____11921 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____11952,uu____11953) ->
                   let rec may_relate head3 =
                     let uu____11978 =
                       let uu____11979 = FStar_Syntax_Subst.compress head3 in
                       uu____11979.FStar_Syntax_Syntax.n in
                     match uu____11978 with
                     | FStar_Syntax_Syntax.Tm_name uu____11982 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____11983 -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____12006;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_equational ;
                           FStar_Syntax_Syntax.fv_qual = uu____12007;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____12010;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_abstract uu____12011;
                           FStar_Syntax_Syntax.fv_qual = uu____12012;_}
                         ->
                         problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____12016,uu____12017) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____12059) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____12065) ->
                         may_relate t
                     | uu____12070 -> false in
                   let uu____12071 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____12071
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
                                let uu____12088 =
                                  let uu____12089 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____12089 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____12088 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____12091 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____12091
                   else
                     (let uu____12093 =
                        let uu____12094 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____12095 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____12094 uu____12095 in
                      giveup env1 uu____12093 orig)
               | (uu____12096,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___142_12110 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___142_12110.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___142_12110.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___142_12110.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___142_12110.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___142_12110.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___142_12110.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___142_12110.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___142_12110.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____12111,FStar_Pervasives_Native.None ) ->
                   ((let uu____12123 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____12123
                     then
                       let uu____12124 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____12125 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____12126 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____12127 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____12124
                         uu____12125 uu____12126 uu____12127
                     else ());
                    (let uu____12129 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____12129 with
                     | (head11,args1) ->
                         let uu____12166 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____12166 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____12220 =
                                  let uu____12221 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____12222 = args_to_string args1 in
                                  let uu____12223 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____12224 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____12221 uu____12222 uu____12223
                                    uu____12224 in
                                giveup env1 uu____12220 orig
                              else
                                (let uu____12226 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____12232 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____12232 = FStar_Syntax_Util.Equal) in
                                 if uu____12226
                                 then
                                   let uu____12233 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____12233 with
                                   | USolved wl2 ->
                                       let uu____12235 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____12235
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____12239 =
                                      base_and_refinement env1 t1 in
                                    match uu____12239 with
                                    | (base1,refinement1) ->
                                        let uu____12264 =
                                          base_and_refinement env1 t2 in
                                        (match uu____12264 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____12321 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____12321 with
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
                                                           (fun uu____12343 
                                                              ->
                                                              fun uu____12344
                                                                 ->
                                                                match 
                                                                  (uu____12343,
                                                                    uu____12344)
                                                                with
                                                                | ((a,uu____12362),
                                                                   (a',uu____12364))
                                                                    ->
                                                                    let uu____12373
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
                                                                    uu____12373)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____12383 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____12383 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____12389 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___143_12425 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___143_12425.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___143_12425.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___143_12425.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___143_12425.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___143_12425.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___143_12425.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___143_12425.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___143_12425.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let force_quasi_pattern xs_opt uu____12458 =
          match uu____12458 with
          | (t,u,k,args) ->
              let debug1 f =
                let uu____12500 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel") in
                if uu____12500 then f () else () in
              let rec aux pat_args pat_args_set pattern_vars pattern_var_set
                seen_formals formals res_t args1 =
                debug1
                  (fun uu____12596  ->
                     let uu____12597 =
                       FStar_Syntax_Print.binders_to_string ", " pat_args in
                     FStar_Util.print1 "pat_args so far: {%s}\n" uu____12597);
                (match (formals, args1) with
                 | ([],[]) ->
                     let pat_args1 =
                       FStar_All.pipe_right (FStar_List.rev pat_args)
                         (FStar_List.map
                            (fun uu____12665  ->
                               match uu____12665 with
                               | (x,imp) ->
                                   let uu____12676 =
                                     FStar_Syntax_Syntax.bv_to_name x in
                                   (uu____12676, imp))) in
                     let pattern_vars1 = FStar_List.rev pattern_vars in
                     let kk =
                       let uu____12689 = FStar_Syntax_Util.type_u () in
                       match uu____12689 with
                       | (t1,uu____12695) ->
                           let uu____12696 =
                             new_uvar t1.FStar_Syntax_Syntax.pos
                               pattern_vars1 t1 in
                           FStar_Pervasives_Native.fst uu____12696 in
                     let uu____12701 =
                       new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk in
                     (match uu____12701 with
                      | (t',tm_u1) ->
                          let uu____12714 = destruct_flex_t t' in
                          (match uu____12714 with
                           | (uu____12751,u1,k1,uu____12754) ->
                               let all_formals = FStar_List.rev seen_formals in
                               let k2 =
                                 let uu____12813 =
                                   FStar_Syntax_Syntax.mk_Total res_t in
                                 FStar_Syntax_Util.arrow all_formals
                                   uu____12813 in
                               let sol =
                                 let uu____12817 =
                                   let uu____12826 = u_abs k2 all_formals t' in
                                   ((u, k2), uu____12826) in
                                 TERM uu____12817 in
                               let t_app =
                                 FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                   pat_args1 FStar_Pervasives_Native.None
                                   t.FStar_Syntax_Syntax.pos in
                               FStar_Pervasives_Native.Some
                                 (sol, (t_app, u1, k1, pat_args1))))
                 | (formal::formals1,hd1::tl1) ->
                     (debug1
                        (fun uu____12961  ->
                           let uu____12962 =
                             FStar_Syntax_Print.binder_to_string formal in
                           let uu____12963 =
                             FStar_Syntax_Print.args_to_string [hd1] in
                           FStar_Util.print2
                             "force_quasi_pattern (case 2): formal=%s, hd=%s\n"
                             uu____12962 uu____12963);
                      (let uu____12976 = pat_var_opt env pat_args hd1 in
                       match uu____12976 with
                       | FStar_Pervasives_Native.None  ->
                           (debug1
                              (fun uu____12996  ->
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
                                      (fun uu____13039  ->
                                         match uu____13039 with
                                         | (x,uu____13045) ->
                                             FStar_Syntax_Syntax.bv_eq x
                                               (FStar_Pervasives_Native.fst y))) in
                           if Prims.op_Negation maybe_pat
                           then
                             aux pat_args pat_args_set pattern_vars
                               pattern_var_set (formal :: seen_formals)
                               formals1 res_t tl1
                           else
                             (debug1
                                (fun uu____13060  ->
                                   let uu____13061 =
                                     FStar_Syntax_Print.args_to_string [hd1] in
                                   let uu____13074 =
                                     FStar_Syntax_Print.binder_to_string y in
                                   FStar_Util.print2
                                     "%s (var = %s) maybe pat\n" uu____13061
                                     uu____13074);
                              (let fvs =
                                 FStar_Syntax_Free.names
                                   (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort in
                               let uu____13078 =
                                 let uu____13079 =
                                   FStar_Util.set_is_subset_of fvs
                                     pat_args_set in
                                 Prims.op_Negation uu____13079 in
                               if uu____13078
                               then
                                 (debug1
                                    (fun uu____13091  ->
                                       let uu____13092 =
                                         let uu____13095 =
                                           FStar_Syntax_Print.args_to_string
                                             [hd1] in
                                         let uu____13108 =
                                           let uu____13111 =
                                             FStar_Syntax_Print.binder_to_string
                                               y in
                                           let uu____13112 =
                                             let uu____13115 =
                                               FStar_Syntax_Print.term_to_string
                                                 (FStar_Pervasives_Native.fst
                                                    y).FStar_Syntax_Syntax.sort in
                                             let uu____13116 =
                                               let uu____13119 =
                                                 names_to_string fvs in
                                               let uu____13120 =
                                                 let uu____13123 =
                                                   names_to_string
                                                     pattern_var_set in
                                                 [uu____13123] in
                                               uu____13119 :: uu____13120 in
                                             uu____13115 :: uu____13116 in
                                           uu____13111 :: uu____13112 in
                                         uu____13095 :: uu____13108 in
                                       FStar_Util.print
                                         "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n"
                                         uu____13092);
                                  aux pat_args pat_args_set pattern_vars
                                    pattern_var_set (formal :: seen_formals)
                                    formals1 res_t tl1)
                               else
                                 (let uu____13125 =
                                    FStar_Util.set_add
                                      (FStar_Pervasives_Native.fst y)
                                      pat_args_set in
                                  let uu____13128 =
                                    FStar_Util.set_add
                                      (FStar_Pervasives_Native.fst formal)
                                      pattern_var_set in
                                  aux (y :: pat_args) uu____13125 (formal ::
                                    pattern_vars) uu____13128 (formal ::
                                    seen_formals) formals1 res_t tl1)))))
                 | ([],uu____13135::uu____13136) ->
                     let uu____13167 =
                       let uu____13180 =
                         FStar_TypeChecker_Normalize.unfold_whnf env res_t in
                       FStar_Syntax_Util.arrow_formals uu____13180 in
                     (match uu____13167 with
                      | (more_formals,res_t1) ->
                          (match more_formals with
                           | [] -> FStar_Pervasives_Native.None
                           | uu____13219 ->
                               aux pat_args pat_args_set pattern_vars
                                 pattern_var_set seen_formals more_formals
                                 res_t1 args1))
                 | (uu____13226::uu____13227,[]) ->
                     FStar_Pervasives_Native.None) in
              let uu____13250 =
                let uu____13263 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k in
                FStar_Syntax_Util.arrow_formals uu____13263 in
              (match uu____13250 with
               | (all_formals,res_t) ->
                   (debug1
                      (fun uu____13299  ->
                         let uu____13300 =
                           FStar_Syntax_Print.term_to_string t in
                         let uu____13301 =
                           FStar_Syntax_Print.binders_to_string ", "
                             all_formals in
                         let uu____13302 =
                           FStar_Syntax_Print.term_to_string res_t in
                         let uu____13303 =
                           FStar_Syntax_Print.args_to_string args in
                         FStar_Util.print4
                           "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n"
                           uu____13300 uu____13301 uu____13302 uu____13303);
                    (let uu____13304 = FStar_Syntax_Syntax.new_bv_set () in
                     let uu____13307 = FStar_Syntax_Syntax.new_bv_set () in
                     aux [] uu____13304 [] uu____13307 [] all_formals res_t
                       args))) in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____13341 = lhs in
          match uu____13341 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____13351 ->
                    let uu____13352 = sn_binders env1 pat_vars1 in
                    u_abs k_uv uu____13352 rhs in
              let wl2 =
                solve_prob orig FStar_Pervasives_Native.None
                  [TERM ((uv, k_uv), sol)] wl1 in
              solve env1 wl2 in
        let imitate orig env1 wl1 p =
          let uu____13375 = p in
          match uu____13375 with
          | (((u,k),xs,c),ps,(h,uu____13386,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13468 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____13468 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13491 = h gs_xs in
                     let uu____13492 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57) in
                     FStar_Syntax_Util.abs xs1 uu____13491 uu____13492 in
                   ((let uu____13498 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____13498
                     then
                       let uu____13499 =
                         let uu____13502 =
                           let uu____13503 =
                             FStar_List.map tc_to_string gs_xs in
                           FStar_All.pipe_right uu____13503
                             (FStar_String.concat "\n\t>") in
                         let uu____13508 =
                           let uu____13511 =
                             FStar_Syntax_Print.binders_to_string ", " xs1 in
                           let uu____13512 =
                             let uu____13515 =
                               FStar_Syntax_Print.comp_to_string c in
                             let uu____13516 =
                               let uu____13519 =
                                 FStar_Syntax_Print.term_to_string im in
                               let uu____13520 =
                                 let uu____13523 =
                                   FStar_Syntax_Print.tag_of_term im in
                                 let uu____13524 =
                                   let uu____13527 =
                                     let uu____13528 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs in
                                     FStar_All.pipe_right uu____13528
                                       (FStar_String.concat ", ") in
                                   let uu____13533 =
                                     let uu____13536 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula in
                                     [uu____13536] in
                                   uu____13527 :: uu____13533 in
                                 uu____13523 :: uu____13524 in
                               uu____13519 :: uu____13520 in
                             uu____13515 :: uu____13516 in
                           uu____13511 :: uu____13512 in
                         uu____13502 :: uu____13508 in
                       FStar_Util.print
                         "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13499
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___107_13557 =
          match uu___107_13557 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____13589 = p in
          match uu____13589 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13680 = FStar_List.nth ps i in
              (match uu____13680 with
               | (pi,uu____13684) ->
                   let uu____13689 = FStar_List.nth xs i in
                   (match uu____13689 with
                    | (xi,uu____13701) ->
                        let rec gs k =
                          let uu____13714 =
                            let uu____13727 =
                              FStar_TypeChecker_Normalize.unfold_whnf env1 k in
                            FStar_Syntax_Util.arrow_formals uu____13727 in
                          match uu____13714 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____13802)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____13815 = new_uvar r xs k_a in
                                    (match uu____13815 with
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
                                         let uu____13837 = aux subst2 tl1 in
                                         (match uu____13837 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____13864 =
                                                let uu____13867 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____13867 :: gi_xs' in
                                              let uu____13868 =
                                                let uu____13871 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____13871 :: gi_ps' in
                                              (uu____13864, uu____13868))) in
                              aux [] bs in
                        let uu____13876 =
                          let uu____13877 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____13877 in
                        if uu____13876
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____13881 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____13881 with
                           | (g_xs,uu____13893) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____13904 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____13905 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_58  ->
                                        FStar_Pervasives_Native.Some _0_58) in
                                 FStar_Syntax_Util.abs xs uu____13904
                                   uu____13905 in
                               let sub1 =
                                 let uu____13911 =
                                   let uu____13916 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____13919 =
                                     let uu____13922 =
                                       FStar_List.map
                                         (fun uu____13937  ->
                                            match uu____13937 with
                                            | (uu____13946,uu____13947,y) ->
                                                y) qs in
                                     FStar_All.pipe_left h uu____13922 in
                                   mk_problem (p_scope orig) orig uu____13916
                                     (p_rel orig) uu____13919
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____13911 in
                               ((let uu____13962 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____13962
                                 then
                                   let uu____13963 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____13964 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____13963 uu____13964
                                 else ());
                                (let wl2 =
                                   let uu____13967 =
                                     let uu____13970 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____13970 in
                                   solve_prob orig uu____13967
                                     [TERM (u, proj)] wl1 in
                                 let uu____13979 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____13979))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____14010 = lhs in
          match uu____14010 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____14046 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____14046 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____14079 =
                        let uu____14126 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____14126) in
                      FStar_Pervasives_Native.Some uu____14079
                    else
                      (let rec elim k args =
                         let k1 =
                           FStar_TypeChecker_Normalize.unfold_whnf env k in
                         let uu____14270 =
                           let uu____14277 =
                             let uu____14278 = FStar_Syntax_Subst.compress k1 in
                             uu____14278.FStar_Syntax_Syntax.n in
                           (uu____14277, args) in
                         match uu____14270 with
                         | (uu____14289,[]) ->
                             let uu____14292 =
                               let uu____14303 =
                                 FStar_Syntax_Syntax.mk_Total k1 in
                               ([], uu____14303) in
                             FStar_Pervasives_Native.Some uu____14292
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____14324,uu____14325) ->
                             let uu____14346 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14346 with
                              | (uv1,uv_args) ->
                                  let uu____14389 =
                                    let uu____14390 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14390.FStar_Syntax_Syntax.n in
                                  (match uu____14389 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14400) ->
                                       let uu____14425 =
                                         pat_vars env [] uv_args in
                                       (match uu____14425 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14452  ->
                                                      let uu____14453 =
                                                        let uu____14454 =
                                                          let uu____14455 =
                                                            let uu____14460 =
                                                              let uu____14461
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14461
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14460 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14455 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14454 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14453)) in
                                            let c1 =
                                              let uu____14471 =
                                                let uu____14472 =
                                                  let uu____14477 =
                                                    let uu____14478 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14478
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14477 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14472 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14471 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14491 =
                                                let uu____14494 =
                                                  let uu____14495 =
                                                    let uu____14498 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14498
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14495 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14494 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14491 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14516 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14521,uu____14522) ->
                             let uu____14541 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14541 with
                              | (uv1,uv_args) ->
                                  let uu____14584 =
                                    let uu____14585 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14585.FStar_Syntax_Syntax.n in
                                  (match uu____14584 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14595) ->
                                       let uu____14620 =
                                         pat_vars env [] uv_args in
                                       (match uu____14620 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14647  ->
                                                      let uu____14648 =
                                                        let uu____14649 =
                                                          let uu____14650 =
                                                            let uu____14655 =
                                                              let uu____14656
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14656
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14655 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14650 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14649 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14648)) in
                                            let c1 =
                                              let uu____14666 =
                                                let uu____14667 =
                                                  let uu____14672 =
                                                    let uu____14673 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14673
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14672 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14667 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14666 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14686 =
                                                let uu____14689 =
                                                  let uu____14690 =
                                                    let uu____14693 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14693
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14690 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14689 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14686 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14711 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____14718) ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____14759 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____14759
                                 (fun _0_61  ->
                                    FStar_Pervasives_Native.Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____14795 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____14795 with
                                  | (args1,rest) ->
                                      let uu____14824 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____14824 with
                                       | (xs2,c2) ->
                                           let uu____14837 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____14837
                                             (fun uu____14861  ->
                                                match uu____14861 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____14901 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____14901 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k1.FStar_Syntax_Syntax.pos in
                                      let uu____14969 =
                                        let uu____14974 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____14974 in
                                      FStar_All.pipe_right uu____14969
                                        (fun _0_62  ->
                                           FStar_Pervasives_Native.Some _0_62))
                         | uu____14989 ->
                             let uu____14996 =
                               let uu____15001 =
                                 let uu____15002 =
                                   FStar_Syntax_Print.uvar_to_string uv in
                                 let uu____15003 =
                                   FStar_Syntax_Print.term_to_string k1 in
                                 let uu____15004 =
                                   FStar_Syntax_Print.term_to_string k_uv in
                                 FStar_Util.format3
                                   "Impossible: ill-typed application %s : %s\n\t%s"
                                   uu____15002 uu____15003 uu____15004 in
                               (FStar_Errors.Fatal_IllTyped, uu____15001) in
                             FStar_Errors.raise_error uu____14996
                               t1.FStar_Syntax_Syntax.pos in
                       let uu____15011 = elim k_uv ps in
                       FStar_Util.bind_opt uu____15011
                         (fun uu____15066  ->
                            match uu____15066 with
                            | (xs1,c1) ->
                                let uu____15115 =
                                  let uu____15156 = decompose env t2 in
                                  (((uv, k_uv), xs1, c1), ps, uu____15156) in
                                FStar_Pervasives_Native.Some uu____15115)) in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail uu____15277 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig in
                let rec try_project st i =
                  if i >= n1
                  then fail ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction () in
                     let uu____15293 = project orig env wl1 i st in
                     match uu____15293 with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some (Failed uu____15307) ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some sol -> sol) in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt in
                  let tx = FStar_Syntax_Unionfind.new_transaction () in
                  let uu____15322 = imitate orig env wl1 st in
                  match uu____15322 with
                  | Failed uu____15327 ->
                      (FStar_Syntax_Unionfind.rollback tx;
                       try_project st (Prims.parse_int "0"))
                  | sol -> sol
                else fail () in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____15358 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1 in
                match uu____15358 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let uu____15381 = forced_lhs_pattern in
                    (match uu____15381 with
                     | (lhs_t,uu____15383,uu____15384,uu____15385) ->
                         ((let uu____15387 =
                             FStar_TypeChecker_Env.debug env
                               (FStar_Options.Other "Rel") in
                           if uu____15387
                           then
                             let uu____15388 = lhs1 in
                             match uu____15388 with
                             | (t0,uu____15390,uu____15391,uu____15392) ->
                                 let uu____15393 = forced_lhs_pattern in
                                 (match uu____15393 with
                                  | (t11,uu____15395,uu____15396,uu____15397)
                                      ->
                                      let uu____15398 =
                                        FStar_Syntax_Print.term_to_string t0 in
                                      let uu____15399 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      FStar_Util.print2
                                        "force_quasi_pattern succeeded, turning %s into %s\n"
                                        uu____15398 uu____15399)
                           else ());
                          (let rhs_vars = FStar_Syntax_Free.names rhs in
                           let lhs_vars = FStar_Syntax_Free.names lhs_t in
                           let uu____15407 =
                             FStar_Util.set_is_subset_of rhs_vars lhs_vars in
                           if uu____15407
                           then
                             ((let uu____15409 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "Rel") in
                               if uu____15409
                               then
                                 let uu____15410 =
                                   FStar_Syntax_Print.term_to_string rhs in
                                 let uu____15411 = names_to_string rhs_vars in
                                 let uu____15412 = names_to_string lhs_vars in
                                 FStar_Util.print3
                                   "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n"
                                   uu____15410 uu____15411 uu____15412
                               else ());
                              (let tx =
                                 FStar_Syntax_Unionfind.new_transaction () in
                               let wl2 =
                                 extend_solution (p_pid orig) [sol] wl1 in
                               let uu____15416 =
                                 let uu____15417 =
                                   FStar_TypeChecker_Common.as_tprob orig in
                                 solve_t env uu____15417 wl2 in
                               match uu____15416 with
                               | Failed uu____15418 ->
                                   (FStar_Syntax_Unionfind.rollback tx;
                                    imitate_or_project n1 lhs1 rhs stopt)
                               | sol1 -> sol1))
                           else
                             ((let uu____15427 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "Rel") in
                               if uu____15427
                               then
                                 FStar_Util.print_string
                                   "fvar check failed for quasi pattern ... im/proj\n"
                               else ());
                              imitate_or_project n1 lhs1 rhs stopt)))) in
              let check_head fvs1 t21 =
                let uu____15440 = FStar_Syntax_Util.head_and_args t21 in
                match uu____15440 with
                | (hd1,uu____15456) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15477 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15490 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15491 -> true
                     | uu____15508 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____15512 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____15512
                         then true
                         else
                           ((let uu____15515 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____15515
                             then
                               let uu____15516 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s\n"
                                 uu____15516
                             else ());
                            false)) in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let lhs1 = (t11, uv, k_uv, args_lhs) in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____15536 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____15536 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15549 =
                            let uu____15550 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____15550 in
                          giveup_or_defer1 orig uu____15549
                        else
                          (let uu____15552 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____15552
                           then
                             let uu____15553 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____15553
                              then
                                let uu____15554 = subterms args_lhs in
                                imitate' orig env wl1 uu____15554
                              else
                                ((let uu____15559 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____15559
                                  then
                                    let uu____15560 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____15561 = names_to_string fvs1 in
                                    let uu____15562 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15560 uu____15561 uu____15562
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
                               (let uu____15566 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____15566
                                then
                                  ((let uu____15568 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____15568
                                    then
                                      let uu____15569 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____15570 = names_to_string fvs1 in
                                      let uu____15571 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                        uu____15569 uu____15570 uu____15571
                                    else ());
                                   (let uu____15573 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) lhs1 t21
                                      uu____15573))
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
                     (let uu____15584 =
                        let uu____15585 = FStar_Syntax_Free.names t1 in
                        check_head uu____15585 t2 in
                      if uu____15584
                      then
                        let n_args_lhs = FStar_List.length args_lhs in
                        ((let uu____15596 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____15596
                          then
                            let uu____15597 =
                              FStar_Syntax_Print.term_to_string t1 in
                            let uu____15598 =
                              FStar_Util.string_of_int n_args_lhs in
                            FStar_Util.print2
                              "Not a pattern (%s) ... (lhs has %s args)\n"
                              uu____15597 uu____15598
                          else ());
                         (let uu____15606 = subterms args_lhs in
                          pattern_eq_imitate_or_project n_args_lhs
                            (FStar_Pervasives_Native.fst lhs) t2 uu____15606))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let solve_both_pats wl1 uu____15683 uu____15684 r =
               match (uu____15683, uu____15684) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____15882 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____15882
                   then
                     let uu____15883 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____15883
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____15907 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____15907
                       then
                         let uu____15908 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____15909 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____15910 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____15911 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____15912 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____15908 uu____15909 uu____15910 uu____15911
                           uu____15912
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____15972 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____15972 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____15986 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____15986 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____16040 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____16040 in
                                  let uu____16043 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____16043 k3)
                           else
                             (let uu____16047 =
                                let uu____16048 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____16049 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____16050 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____16048 uu____16049 uu____16050 in
                              failwith uu____16047) in
                       let uu____16051 =
                         let uu____16058 =
                           let uu____16071 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____16071 in
                         match uu____16058 with
                         | (bs,k1') ->
                             let uu____16096 =
                               let uu____16109 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____16109 in
                             (match uu____16096 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____16137 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____16137 in
                                  let uu____16146 =
                                    let uu____16151 =
                                      let uu____16152 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____16152.FStar_Syntax_Syntax.n in
                                    let uu____16155 =
                                      let uu____16156 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____16156.FStar_Syntax_Syntax.n in
                                    (uu____16151, uu____16155) in
                                  (match uu____16146 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____16165,uu____16166) ->
                                       (k1'_xs, [sub_prob])
                                   | (uu____16169,FStar_Syntax_Syntax.Tm_type
                                      uu____16170) -> (k2'_ys, [sub_prob])
                                   | uu____16173 ->
                                       let uu____16178 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____16178 with
                                        | (t,uu____16190) ->
                                            let uu____16191 = new_uvar r zs t in
                                            (match uu____16191 with
                                             | (k_zs,uu____16203) ->
                                                 let kprob =
                                                   let uu____16205 =
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
                                                          _0_64) uu____16205 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____16051 with
                       | (k_u',sub_probs) ->
                           let uu____16222 =
                             let uu____16233 =
                               let uu____16234 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____16234 in
                             let uu____16243 =
                               let uu____16246 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____16246 in
                             let uu____16249 =
                               let uu____16252 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____16252 in
                             (uu____16233, uu____16243, uu____16249) in
                           (match uu____16222 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____16271 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____16271 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____16290 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____16290
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____16294 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____16294 with
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
             let solve_one_pat uu____16347 uu____16348 =
               match (uu____16347, uu____16348) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____16466 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____16466
                     then
                       let uu____16467 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____16468 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____16467 uu____16468
                     else ());
                    (let uu____16470 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____16470
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16489  ->
                              fun uu____16490  ->
                                match (uu____16489, uu____16490) with
                                | ((a,uu____16508),(t21,uu____16510)) ->
                                    let uu____16519 =
                                      let uu____16524 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____16524
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____16519
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2 in
                       let guard =
                         let uu____16530 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____16530 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____16545 = occurs_check env wl (u1, k1) t21 in
                        match uu____16545 with
                        | (occurs_ok,uu____16553) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____16561 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____16561
                            then
                              let sol =
                                let uu____16563 =
                                  let uu____16572 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____16572) in
                                TERM uu____16563 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____16579 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____16579
                               then
                                 let uu____16580 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____16580 with
                                 | FStar_Pervasives_Native.None  ->
                                     giveup_or_defer1 orig
                                       "flex-flex constraint"
                                 | FStar_Pervasives_Native.Some
                                     (sol,(uu____16604,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____16630 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____16630
                                       then
                                         let uu____16631 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16631
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16638 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____16640 = lhs in
             match uu____16640 with
             | (t1,u1,k1,args1) ->
                 let uu____16645 = rhs in
                 (match uu____16645 with
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
                       | uu____16685 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16695 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____16695 with
                              | FStar_Pervasives_Native.None  ->
                                  giveup env
                                    "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                    orig
                              | FStar_Pervasives_Native.Some
                                  (sol,uu____16713) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____16720 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____16720
                                    then
                                      let uu____16721 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16721
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16728 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____16730 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____16730
        then
          let uu____16731 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____16731
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____16735 = FStar_Util.physical_equality t1 t2 in
           if uu____16735
           then
             let uu____16736 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____16736
           else
             ((let uu____16739 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____16739
               then
                 let uu____16740 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____16740
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_ascribed uu____16743,uu____16744) ->
                   let uu____16771 =
                     let uu___144_16772 = problem in
                     let uu____16773 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___144_16772.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16773;
                       FStar_TypeChecker_Common.relation =
                         (uu___144_16772.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___144_16772.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___144_16772.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___144_16772.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___144_16772.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___144_16772.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___144_16772.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___144_16772.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16771 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____16774,uu____16775) ->
                   let uu____16782 =
                     let uu___144_16783 = problem in
                     let uu____16784 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___144_16783.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16784;
                       FStar_TypeChecker_Common.relation =
                         (uu___144_16783.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___144_16783.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___144_16783.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___144_16783.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___144_16783.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___144_16783.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___144_16783.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___144_16783.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16782 wl
               | (uu____16785,FStar_Syntax_Syntax.Tm_ascribed uu____16786) ->
                   let uu____16813 =
                     let uu___145_16814 = problem in
                     let uu____16815 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___145_16814.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___145_16814.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___145_16814.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16815;
                       FStar_TypeChecker_Common.element =
                         (uu___145_16814.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___145_16814.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___145_16814.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___145_16814.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___145_16814.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___145_16814.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16813 wl
               | (uu____16816,FStar_Syntax_Syntax.Tm_meta uu____16817) ->
                   let uu____16824 =
                     let uu___145_16825 = problem in
                     let uu____16826 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___145_16825.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___145_16825.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___145_16825.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16826;
                       FStar_TypeChecker_Common.element =
                         (uu___145_16825.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___145_16825.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___145_16825.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___145_16825.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___145_16825.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___145_16825.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16824 wl
               | (FStar_Syntax_Syntax.Tm_bvar uu____16827,uu____16828) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____16829,FStar_Syntax_Syntax.Tm_bvar uu____16830) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___108_16885 =
                     match uu___108_16885 with
                     | [] -> c
                     | bs ->
                         let uu____16907 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____16907 in
                   let uu____16916 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____16916 with
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
                                   let uu____17058 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____17058
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____17060 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____17060))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___109_17136 =
                     match uu___109_17136 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____17170 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____17170 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____17306 =
                                   let uu____17311 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____17312 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____17311
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____17312 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____17306))
               | (FStar_Syntax_Syntax.Tm_abs uu____17317,uu____17318) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17343 -> true
                     | uu____17360 -> false in
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
                       (let uu____17407 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___146_17415 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___146_17415.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___146_17415.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___146_17415.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___146_17415.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___146_17415.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___146_17415.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___146_17415.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___146_17415.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___146_17415.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___146_17415.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___146_17415.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___146_17415.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___146_17415.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___146_17415.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___146_17415.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___146_17415.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___146_17415.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___146_17415.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___146_17415.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___146_17415.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___146_17415.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___146_17415.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___146_17415.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___146_17415.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___146_17415.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___146_17415.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___146_17415.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___146_17415.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___146_17415.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___146_17415.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___146_17415.FStar_TypeChecker_Env.dep_graph)
                             }) t in
                        match uu____17407 with
                        | (uu____17418,ty,uu____17420) ->
                            let uu____17421 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17421) in
                   let uu____17422 =
                     let uu____17439 = maybe_eta t1 in
                     let uu____17446 = maybe_eta t2 in
                     (uu____17439, uu____17446) in
                   (match uu____17422 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___147_17488 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___147_17488.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___147_17488.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___147_17488.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___147_17488.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___147_17488.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___147_17488.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___147_17488.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___147_17488.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17511 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17511
                        then
                          let uu____17512 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17512 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___148_17527 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___148_17527.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___148_17527.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___148_17527.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___148_17527.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___148_17527.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___148_17527.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___148_17527.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___148_17527.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17551 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17551
                        then
                          let uu____17552 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17552 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___148_17567 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___148_17567.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___148_17567.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___148_17567.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___148_17567.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___148_17567.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___148_17567.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___148_17567.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___148_17567.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17571 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17588,FStar_Syntax_Syntax.Tm_abs uu____17589) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17614 -> true
                     | uu____17631 -> false in
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
                       (let uu____17678 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___146_17686 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___146_17686.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___146_17686.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___146_17686.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___146_17686.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___146_17686.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___146_17686.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___146_17686.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___146_17686.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___146_17686.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___146_17686.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___146_17686.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___146_17686.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___146_17686.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___146_17686.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___146_17686.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___146_17686.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___146_17686.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___146_17686.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___146_17686.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___146_17686.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___146_17686.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___146_17686.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___146_17686.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___146_17686.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___146_17686.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___146_17686.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___146_17686.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___146_17686.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___146_17686.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___146_17686.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___146_17686.FStar_TypeChecker_Env.dep_graph)
                             }) t in
                        match uu____17678 with
                        | (uu____17689,ty,uu____17691) ->
                            let uu____17692 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17692) in
                   let uu____17693 =
                     let uu____17710 = maybe_eta t1 in
                     let uu____17717 = maybe_eta t2 in
                     (uu____17710, uu____17717) in
                   (match uu____17693 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___147_17759 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___147_17759.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___147_17759.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___147_17759.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___147_17759.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___147_17759.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___147_17759.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___147_17759.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___147_17759.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17782 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17782
                        then
                          let uu____17783 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17783 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___148_17798 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___148_17798.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___148_17798.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___148_17798.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___148_17798.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___148_17798.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___148_17798.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___148_17798.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___148_17798.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17822 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17822
                        then
                          let uu____17823 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17823 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___148_17838 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___148_17838.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___148_17838.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___148_17838.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___148_17838.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___148_17838.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___148_17838.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___148_17838.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___148_17838.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17842 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                   let should_delta =
                     ((let uu____17874 = FStar_Syntax_Free.uvars t1 in
                       FStar_Util.set_is_empty uu____17874) &&
                        (let uu____17886 = FStar_Syntax_Free.uvars t2 in
                         FStar_Util.set_is_empty uu____17886))
                       &&
                       (let uu____17901 =
                          head_matches env x1.FStar_Syntax_Syntax.sort
                            x2.FStar_Syntax_Syntax.sort in
                        match uu____17901 with
                        | MisMatch
                            (FStar_Pervasives_Native.Some
                             d1,FStar_Pervasives_Native.Some d2)
                            ->
                            let is_unfoldable uu___110_17911 =
                              match uu___110_17911 with
                              | FStar_Syntax_Syntax.Delta_constant  -> true
                              | FStar_Syntax_Syntax.Delta_defined_at_level
                                  uu____17912 -> true
                              | uu____17913 -> false in
                            (is_unfoldable d1) && (is_unfoldable d2)
                        | uu____17914 -> false) in
                   let uu____17915 = as_refinement should_delta env wl t1 in
                   (match uu____17915 with
                    | (x11,phi1) ->
                        let uu____17922 =
                          as_refinement should_delta env wl t2 in
                        (match uu____17922 with
                         | (x21,phi21) ->
                             let base_prob =
                               let uu____17930 =
                                 mk_problem (p_scope orig) orig
                                   x11.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x21.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____17930 in
                             let x12 = FStar_Syntax_Syntax.freshen_bv x11 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x12)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi22 =
                               FStar_Syntax_Subst.subst subst1 phi21 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x12 in
                             let mk_imp1 imp phi12 phi23 =
                               let uu____17968 = imp phi12 phi23 in
                               FStar_All.pipe_right uu____17968
                                 (guard_on_element wl problem x12) in
                             let fallback uu____17972 =
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
                                 let uu____17978 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____17978 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____17987 =
                                   let uu____17992 =
                                     let uu____17993 =
                                       let uu____18000 =
                                         FStar_Syntax_Syntax.mk_binder x12 in
                                       [uu____18000] in
                                     FStar_List.append (p_scope orig)
                                       uu____17993 in
                                   mk_problem uu____17992 orig phi11
                                     FStar_TypeChecker_Common.EQ phi22
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____17987 in
                               let uu____18009 =
                                 solve env1
                                   (let uu___149_18011 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___149_18011.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___149_18011.smt_ok);
                                      tcenv = (uu___149_18011.tcenv)
                                    }) in
                               (match uu____18009 with
                                | Failed uu____18018 -> fallback ()
                                | Success uu____18023 ->
                                    let guard =
                                      let uu____18027 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____18032 =
                                        let uu____18033 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____18033
                                          (guard_on_element wl problem x12) in
                                      FStar_Syntax_Util.mk_conj uu____18027
                                        uu____18032 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___150_18042 = wl1 in
                                      {
                                        attempting =
                                          (uu___150_18042.attempting);
                                        wl_deferred =
                                          (uu___150_18042.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___150_18042.defer_ok);
                                        smt_ok = (uu___150_18042.smt_ok);
                                        tcenv = (uu___150_18042.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18044,FStar_Syntax_Syntax.Tm_uvar uu____18045) ->
                   let uu____18078 = destruct_flex_t t1 in
                   let uu____18079 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18078 uu____18079
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18080;
                     FStar_Syntax_Syntax.pos = uu____18081;
                     FStar_Syntax_Syntax.vars = uu____18082;_},uu____18083),FStar_Syntax_Syntax.Tm_uvar
                  uu____18084) ->
                   let uu____18137 = destruct_flex_t t1 in
                   let uu____18138 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18137 uu____18138
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18139,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18140;
                     FStar_Syntax_Syntax.pos = uu____18141;
                     FStar_Syntax_Syntax.vars = uu____18142;_},uu____18143))
                   ->
                   let uu____18196 = destruct_flex_t t1 in
                   let uu____18197 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18196 uu____18197
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18198;
                     FStar_Syntax_Syntax.pos = uu____18199;
                     FStar_Syntax_Syntax.vars = uu____18200;_},uu____18201),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18202;
                     FStar_Syntax_Syntax.pos = uu____18203;
                     FStar_Syntax_Syntax.vars = uu____18204;_},uu____18205))
                   ->
                   let uu____18278 = destruct_flex_t t1 in
                   let uu____18279 = destruct_flex_t t2 in
                   flex_flex1 orig uu____18278 uu____18279
               | (FStar_Syntax_Syntax.Tm_uvar uu____18280,uu____18281) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18298 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18298 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18305;
                     FStar_Syntax_Syntax.pos = uu____18306;
                     FStar_Syntax_Syntax.vars = uu____18307;_},uu____18308),uu____18309)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18346 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18346 t2 wl
               | (uu____18353,FStar_Syntax_Syntax.Tm_uvar uu____18354) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____18371,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18372;
                     FStar_Syntax_Syntax.pos = uu____18373;
                     FStar_Syntax_Syntax.vars = uu____18374;_},uu____18375))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18412,FStar_Syntax_Syntax.Tm_type uu____18413) ->
                   solve_t' env
                     (let uu___151_18431 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___151_18431.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___151_18431.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___151_18431.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___151_18431.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___151_18431.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___151_18431.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___151_18431.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___151_18431.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___151_18431.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18432;
                     FStar_Syntax_Syntax.pos = uu____18433;
                     FStar_Syntax_Syntax.vars = uu____18434;_},uu____18435),FStar_Syntax_Syntax.Tm_type
                  uu____18436) ->
                   solve_t' env
                     (let uu___151_18474 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___151_18474.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___151_18474.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___151_18474.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___151_18474.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___151_18474.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___151_18474.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___151_18474.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___151_18474.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___151_18474.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18475,FStar_Syntax_Syntax.Tm_arrow uu____18476) ->
                   solve_t' env
                     (let uu___151_18506 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___151_18506.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___151_18506.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___151_18506.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___151_18506.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___151_18506.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___151_18506.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___151_18506.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___151_18506.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___151_18506.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18507;
                     FStar_Syntax_Syntax.pos = uu____18508;
                     FStar_Syntax_Syntax.vars = uu____18509;_},uu____18510),FStar_Syntax_Syntax.Tm_arrow
                  uu____18511) ->
                   solve_t' env
                     (let uu___151_18561 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___151_18561.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___151_18561.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___151_18561.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___151_18561.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___151_18561.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___151_18561.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___151_18561.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___151_18561.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___151_18561.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18562,uu____18563) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18582 =
                        let uu____18583 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18583 in
                      if uu____18582
                      then
                        let uu____18584 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___152_18590 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___152_18590.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___152_18590.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___152_18590.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___152_18590.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___152_18590.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___152_18590.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___152_18590.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___152_18590.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___152_18590.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18591 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18584 uu____18591 t2
                          wl
                      else
                        (let uu____18599 = base_and_refinement env t2 in
                         match uu____18599 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18628 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___153_18634 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___153_18634.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___153_18634.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___153_18634.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___153_18634.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___153_18634.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___153_18634.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___153_18634.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___153_18634.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___153_18634.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18635 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18628
                                    uu____18635 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___154_18649 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___154_18649.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___154_18649.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18652 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_72  ->
                                         FStar_TypeChecker_Common.TProb _0_72)
                                      uu____18652 in
                                  let guard =
                                    let uu____18664 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18664
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18672;
                     FStar_Syntax_Syntax.pos = uu____18673;
                     FStar_Syntax_Syntax.vars = uu____18674;_},uu____18675),uu____18676)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18715 =
                        let uu____18716 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18716 in
                      if uu____18715
                      then
                        let uu____18717 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___152_18723 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___152_18723.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___152_18723.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___152_18723.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___152_18723.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___152_18723.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___152_18723.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___152_18723.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___152_18723.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___152_18723.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18724 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18717 uu____18724 t2
                          wl
                      else
                        (let uu____18732 = base_and_refinement env t2 in
                         match uu____18732 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18761 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___153_18767 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___153_18767.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___153_18767.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___153_18767.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___153_18767.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___153_18767.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___153_18767.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___153_18767.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___153_18767.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___153_18767.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18768 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18761
                                    uu____18768 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___154_18782 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___154_18782.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___154_18782.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18785 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_75  ->
                                         FStar_TypeChecker_Common.TProb _0_75)
                                      uu____18785 in
                                  let guard =
                                    let uu____18797 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18797
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18805,FStar_Syntax_Syntax.Tm_uvar uu____18806) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18824 = base_and_refinement env t1 in
                      match uu____18824 with
                      | (t_base,uu____18836) ->
                          solve_t env
                            (let uu___155_18850 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___155_18850.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___155_18850.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___155_18850.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___155_18850.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___155_18850.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___155_18850.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___155_18850.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___155_18850.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18851,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18852;
                     FStar_Syntax_Syntax.pos = uu____18853;
                     FStar_Syntax_Syntax.vars = uu____18854;_},uu____18855))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18893 = base_and_refinement env t1 in
                      match uu____18893 with
                      | (t_base,uu____18905) ->
                          solve_t env
                            (let uu___155_18919 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___155_18919.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___155_18919.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___155_18919.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___155_18919.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___155_18919.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___155_18919.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___155_18919.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___155_18919.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____18920,uu____18921) ->
                   let t21 =
                     let uu____18931 = base_and_refinement env t2 in
                     FStar_All.pipe_left force_refinement uu____18931 in
                   solve_t env
                     (let uu___156_18955 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___156_18955.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___156_18955.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___156_18955.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___156_18955.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___156_18955.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___156_18955.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___156_18955.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___156_18955.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___156_18955.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____18956,FStar_Syntax_Syntax.Tm_refine uu____18957) ->
                   let t11 =
                     let uu____18967 = base_and_refinement env t1 in
                     FStar_All.pipe_left force_refinement uu____18967 in
                   solve_t env
                     (let uu___157_18991 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___157_18991.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___157_18991.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___157_18991.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___157_18991.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___157_18991.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___157_18991.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___157_18991.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___157_18991.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___157_18991.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____18994,uu____18995) ->
                   let head1 =
                     let uu____19021 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19021
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19065 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19065
                       FStar_Pervasives_Native.fst in
                   let uu____19106 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19106
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19121 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19121
                      then
                        let guard =
                          let uu____19133 =
                            let uu____19134 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19134 = FStar_Syntax_Util.Equal in
                          if uu____19133
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19138 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____19138) in
                        let uu____19141 = solve_prob orig guard [] wl in
                        solve env uu____19141
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____19144,uu____19145) ->
                   let head1 =
                     let uu____19155 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19155
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19199 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19199
                       FStar_Pervasives_Native.fst in
                   let uu____19240 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19240
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19255 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19255
                      then
                        let guard =
                          let uu____19267 =
                            let uu____19268 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19268 = FStar_Syntax_Util.Equal in
                          if uu____19267
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19272 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____19272) in
                        let uu____19275 = solve_prob orig guard [] wl in
                        solve env uu____19275
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____19278,uu____19279) ->
                   let head1 =
                     let uu____19283 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19283
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19327 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19327
                       FStar_Pervasives_Native.fst in
                   let uu____19368 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19368
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19383 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19383
                      then
                        let guard =
                          let uu____19395 =
                            let uu____19396 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19396 = FStar_Syntax_Util.Equal in
                          if uu____19395
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19400 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____19400) in
                        let uu____19403 = solve_prob orig guard [] wl in
                        solve env uu____19403
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____19406,uu____19407) ->
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
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____19528) in
                        let uu____19531 = solve_prob orig guard [] wl in
                        solve env uu____19531
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____19534,uu____19535) ->
                   let head1 =
                     let uu____19539 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19539
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19583 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19583
                       FStar_Pervasives_Native.fst in
                   let uu____19624 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19624
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19639 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19639
                      then
                        let guard =
                          let uu____19651 =
                            let uu____19652 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19652 = FStar_Syntax_Util.Equal in
                          if uu____19651
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19656 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19656) in
                        let uu____19659 = solve_prob orig guard [] wl in
                        solve env uu____19659
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19662,uu____19663) ->
                   let head1 =
                     let uu____19681 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19681
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19725 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19725
                       FStar_Pervasives_Native.fst in
                   let uu____19766 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19766
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19781 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19781
                      then
                        let guard =
                          let uu____19793 =
                            let uu____19794 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19794 = FStar_Syntax_Util.Equal in
                          if uu____19793
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19798 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19798) in
                        let uu____19801 = solve_prob orig guard [] wl in
                        solve env uu____19801
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19804,FStar_Syntax_Syntax.Tm_match uu____19805) ->
                   let head1 =
                     let uu____19831 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19831
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19875 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19875
                       FStar_Pervasives_Native.fst in
                   let uu____19916 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19916
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19931 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19931
                      then
                        let guard =
                          let uu____19943 =
                            let uu____19944 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19944 = FStar_Syntax_Util.Equal in
                          if uu____19943
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19948 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____19948) in
                        let uu____19951 = solve_prob orig guard [] wl in
                        solve env uu____19951
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19954,FStar_Syntax_Syntax.Tm_uinst uu____19955) ->
                   let head1 =
                     let uu____19965 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19965
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20009 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20009
                       FStar_Pervasives_Native.fst in
                   let uu____20050 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20050
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20065 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20065
                      then
                        let guard =
                          let uu____20077 =
                            let uu____20078 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20078 = FStar_Syntax_Util.Equal in
                          if uu____20077
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20082 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____20082) in
                        let uu____20085 = solve_prob orig guard [] wl in
                        solve env uu____20085
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20088,FStar_Syntax_Syntax.Tm_name uu____20089) ->
                   let head1 =
                     let uu____20093 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20093
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20137 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20137
                       FStar_Pervasives_Native.fst in
                   let uu____20178 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20178
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20193 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20193
                      then
                        let guard =
                          let uu____20205 =
                            let uu____20206 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20206 = FStar_Syntax_Util.Equal in
                          if uu____20205
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20210 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____20210) in
                        let uu____20213 = solve_prob orig guard [] wl in
                        solve env uu____20213
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20216,FStar_Syntax_Syntax.Tm_constant uu____20217) ->
                   let head1 =
                     let uu____20221 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20221
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20265 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20265
                       FStar_Pervasives_Native.fst in
                   let uu____20306 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20306
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20321 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20321
                      then
                        let guard =
                          let uu____20333 =
                            let uu____20334 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20334 = FStar_Syntax_Util.Equal in
                          if uu____20333
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20338 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____20338) in
                        let uu____20341 = solve_prob orig guard [] wl in
                        solve env uu____20341
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20344,FStar_Syntax_Syntax.Tm_fvar uu____20345) ->
                   let head1 =
                     let uu____20349 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20349
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20393 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20393
                       FStar_Pervasives_Native.fst in
                   let uu____20434 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20434
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20449 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20449
                      then
                        let guard =
                          let uu____20461 =
                            let uu____20462 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20462 = FStar_Syntax_Util.Equal in
                          if uu____20461
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20466 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____20466) in
                        let uu____20469 = solve_prob orig guard [] wl in
                        solve env uu____20469
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20472,FStar_Syntax_Syntax.Tm_app uu____20473) ->
                   let head1 =
                     let uu____20491 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20491
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20535 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20535
                       FStar_Pervasives_Native.fst in
                   let uu____20576 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20576
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20591 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20591
                      then
                        let guard =
                          let uu____20603 =
                            let uu____20604 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20604 = FStar_Syntax_Util.Equal in
                          if uu____20603
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20608 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____20608) in
                        let uu____20611 = solve_prob orig guard [] wl in
                        solve env uu____20611
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let uu____20614,uu____20615) ->
                   let uu____20628 =
                     let uu____20629 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20630 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20629
                       uu____20630 in
                   failwith uu____20628
               | (FStar_Syntax_Syntax.Tm_delayed uu____20631,uu____20632) ->
                   let uu____20657 =
                     let uu____20658 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20659 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20658
                       uu____20659 in
                   failwith uu____20657
               | (uu____20660,FStar_Syntax_Syntax.Tm_delayed uu____20661) ->
                   let uu____20686 =
                     let uu____20687 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20688 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20687
                       uu____20688 in
                   failwith uu____20686
               | (uu____20689,FStar_Syntax_Syntax.Tm_let uu____20690) ->
                   let uu____20703 =
                     let uu____20704 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20705 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20704
                       uu____20705 in
                   failwith uu____20703
               | uu____20706 -> giveup env "head tag mismatch" orig)))
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
          (let uu____20742 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____20742
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____20744 =
               let uu____20745 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name in
               let uu____20746 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20745 uu____20746 in
             giveup env uu____20744 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____20766  ->
                    fun uu____20767  ->
                      match (uu____20766, uu____20767) with
                      | ((a1,uu____20785),(a2,uu____20787)) ->
                          let uu____20796 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg" in
                          FStar_All.pipe_left
                            (fun _0_88  ->
                               FStar_TypeChecker_Common.TProb _0_88)
                            uu____20796)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args in
             let guard =
               let uu____20806 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs in
               FStar_Syntax_Util.mk_conj_l uu____20806 in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
             solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____20830 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20837)::[] -> wp1
              | uu____20854 ->
                  let uu____20863 =
                    let uu____20864 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20864 in
                  failwith uu____20863 in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____20872 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ in
                  [uu____20872]
              | x -> x in
            let uu____20874 =
              let uu____20883 =
                let uu____20884 =
                  let uu____20885 = FStar_List.hd univs1 in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____20885 c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____20884 in
              [uu____20883] in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20874;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20886 = lift_c1 () in solve_eq uu____20886 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___111_20892  ->
                       match uu___111_20892 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20893 -> false)) in
             let uu____20894 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20928)::uu____20929,(wp2,uu____20931)::uu____20932)
                   -> (wp1, wp2)
               | uu____20989 ->
                   let uu____21010 =
                     let uu____21015 =
                       let uu____21016 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name in
                       let uu____21017 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____21016 uu____21017 in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____21015) in
                   FStar_Errors.raise_error uu____21010
                     env.FStar_TypeChecker_Env.range in
             match uu____20894 with
             | (wpc1,wpc2) ->
                 let uu____21036 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____21036
                 then
                   let uu____21039 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____21039 wl
                 else
                   (let uu____21043 =
                      let uu____21050 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____21050 in
                    match uu____21043 with
                    | (c2_decl,qualifiers) ->
                        let uu____21071 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____21071
                        then
                          let c1_repr =
                            let uu____21075 =
                              let uu____21076 =
                                let uu____21077 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____21077 in
                              let uu____21078 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21076 uu____21078 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21075 in
                          let c2_repr =
                            let uu____21080 =
                              let uu____21081 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____21082 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21081 uu____21082 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21080 in
                          let prob =
                            let uu____21084 =
                              let uu____21089 =
                                let uu____21090 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____21091 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____21090
                                  uu____21091 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____21089 in
                            FStar_TypeChecker_Common.TProb uu____21084 in
                          let wl1 =
                            let uu____21093 =
                              let uu____21096 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____21096 in
                            solve_prob orig uu____21093 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____21105 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____21105
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ in
                                   let uu____21108 =
                                     let uu____21111 =
                                       let uu____21112 =
                                         let uu____21127 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____21128 =
                                           let uu____21131 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____21132 =
                                             let uu____21135 =
                                               let uu____21136 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____21136 in
                                             [uu____21135] in
                                           uu____21131 :: uu____21132 in
                                         (uu____21127, uu____21128) in
                                       FStar_Syntax_Syntax.Tm_app uu____21112 in
                                     FStar_Syntax_Syntax.mk uu____21111 in
                                   uu____21108 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ in
                                  let uu____21145 =
                                    let uu____21148 =
                                      let uu____21149 =
                                        let uu____21164 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____21165 =
                                          let uu____21168 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____21169 =
                                            let uu____21172 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____21173 =
                                              let uu____21176 =
                                                let uu____21177 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____21177 in
                                              [uu____21176] in
                                            uu____21172 :: uu____21173 in
                                          uu____21168 :: uu____21169 in
                                        (uu____21164, uu____21165) in
                                      FStar_Syntax_Syntax.Tm_app uu____21149 in
                                    FStar_Syntax_Syntax.mk uu____21148 in
                                  uu____21145 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____21184 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____21184 in
                           let wl1 =
                             let uu____21194 =
                               let uu____21197 =
                                 let uu____21200 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____21200 g in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____21197 in
                             solve_prob orig uu____21194 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____21213 = FStar_Util.physical_equality c1 c2 in
        if uu____21213
        then
          let uu____21214 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____21214
        else
          ((let uu____21217 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____21217
            then
              let uu____21218 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____21219 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____21218
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____21219
            else ());
           (let uu____21221 =
              let uu____21226 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____21227 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____21226, uu____21227) in
            match uu____21221 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21231),FStar_Syntax_Syntax.Total
                    (t2,uu____21233)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21250 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21250 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21253,FStar_Syntax_Syntax.Total uu____21254) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21272),FStar_Syntax_Syntax.Total
                    (t2,uu____21274)) ->
                     let uu____21291 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21291 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21295),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21297)) ->
                     let uu____21314 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21314 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21318),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21320)) ->
                     let uu____21337 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21337 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21340,FStar_Syntax_Syntax.Comp uu____21341) ->
                     let uu____21350 =
                       let uu___158_21355 = problem in
                       let uu____21360 =
                         let uu____21361 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21361 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___158_21355.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21360;
                         FStar_TypeChecker_Common.relation =
                           (uu___158_21355.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___158_21355.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___158_21355.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___158_21355.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___158_21355.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___158_21355.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___158_21355.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___158_21355.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21350 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21362,FStar_Syntax_Syntax.Comp uu____21363) ->
                     let uu____21372 =
                       let uu___158_21377 = problem in
                       let uu____21382 =
                         let uu____21383 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21383 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___158_21377.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21382;
                         FStar_TypeChecker_Common.relation =
                           (uu___158_21377.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___158_21377.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___158_21377.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___158_21377.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___158_21377.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___158_21377.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___158_21377.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___158_21377.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21372 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21384,FStar_Syntax_Syntax.GTotal uu____21385) ->
                     let uu____21394 =
                       let uu___159_21399 = problem in
                       let uu____21404 =
                         let uu____21405 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21405 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___159_21399.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___159_21399.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___159_21399.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21404;
                         FStar_TypeChecker_Common.element =
                           (uu___159_21399.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___159_21399.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___159_21399.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___159_21399.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___159_21399.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___159_21399.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21394 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21406,FStar_Syntax_Syntax.Total uu____21407) ->
                     let uu____21416 =
                       let uu___159_21421 = problem in
                       let uu____21426 =
                         let uu____21427 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21427 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___159_21421.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___159_21421.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___159_21421.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21426;
                         FStar_TypeChecker_Common.element =
                           (uu___159_21421.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___159_21421.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___159_21421.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___159_21421.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___159_21421.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___159_21421.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21416 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21428,FStar_Syntax_Syntax.Comp uu____21429) ->
                     let uu____21430 =
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
                     if uu____21430
                     then
                       let uu____21431 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____21431 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21437 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21447 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____21448 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____21447, uu____21448)) in
                          match uu____21437 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu____21455 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____21455
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21457 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____21457 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21460 =
                                  let uu____21461 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name in
                                  let uu____21462 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____21461 uu____21462 in
                                giveup env uu____21460 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____21467 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21505  ->
              match uu____21505 with
              | (uu____21518,uu____21519,u,uu____21521,uu____21522,uu____21523)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____21467 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____21554 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____21554 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____21572 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21600  ->
                match uu____21600 with
                | (u1,u2) ->
                    let uu____21607 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____21608 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____21607 uu____21608)) in
      FStar_All.pipe_right uu____21572 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21625,[])) -> "{}"
      | uu____21650 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21667 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____21667
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____21670 =
              FStar_List.map
                (fun uu____21680  ->
                   match uu____21680 with
                   | (uu____21685,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____21670 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____21690 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21690 imps
let new_t_problem:
  'Auu____21698 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21698 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21698)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21732 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel") in
                if uu____21732
                then
                  let uu____21733 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs in
                  let uu____21734 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21733
                    (rel_to_string rel) uu____21734
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
            let uu____21758 =
              let uu____21761 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____21761 in
            FStar_Syntax_Syntax.new_bv uu____21758 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____21770 =
              let uu____21773 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____21773 in
            let uu____21776 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____21770 uu____21776 in
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
          let uu____21806 = FStar_Options.eager_inference () in
          if uu____21806
          then
            let uu___160_21807 = probs in
            {
              attempting = (uu___160_21807.attempting);
              wl_deferred = (uu___160_21807.wl_deferred);
              ctr = (uu___160_21807.ctr);
              defer_ok = false;
              smt_ok = (uu___160_21807.smt_ok);
              tcenv = (uu___160_21807.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            ((let uu____21818 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____21818
              then
                let uu____21819 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____21819
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
          ((let uu____21833 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____21833
            then
              let uu____21834 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21834
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f in
            (let uu____21838 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____21838
             then
               let uu____21839 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21839
             else ());
            (let f2 =
               let uu____21842 =
                 let uu____21843 = FStar_Syntax_Util.unmeta f1 in
                 uu____21843.FStar_Syntax_Syntax.n in
               match uu____21842 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21847 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___161_21848 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___161_21848.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___161_21848.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___161_21848.FStar_TypeChecker_Env.implicits)
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
            let uu____21867 =
              let uu____21868 =
                let uu____21869 =
                  let uu____21870 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____21870
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21869;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____21868 in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____21867
let with_guard_no_simp:
  'Auu____21897 .
    'Auu____21897 ->
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
            let uu____21917 =
              let uu____21918 =
                let uu____21919 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____21919
                  (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
              {
                FStar_TypeChecker_Env.guard_f = uu____21918;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              } in
            FStar_Pervasives_Native.Some uu____21917
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
          (let uu____21957 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21957
           then
             let uu____21958 = FStar_Syntax_Print.term_to_string t1 in
             let uu____21959 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21958
               uu____21959
           else ());
          (let prob =
             let uu____21962 =
               let uu____21967 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____21967 in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____21962 in
           let g =
             let uu____21975 =
               let uu____21978 = singleton' env prob smt_ok in
               solve_and_commit env uu____21978
                 (fun uu____21980  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____21975 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21998 = try_teq true env t1 t2 in
        match uu____21998 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____22002 = FStar_TypeChecker_Env.get_range env in
              let uu____22003 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1 in
              FStar_Errors.log_issue uu____22002 uu____22003);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____22010 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____22010
              then
                let uu____22011 = FStar_Syntax_Print.term_to_string t1 in
                let uu____22012 = FStar_Syntax_Print.term_to_string t2 in
                let uu____22013 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____22011
                  uu____22012 uu____22013
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
          let uu____22027 = FStar_TypeChecker_Env.get_range env in
          let uu____22028 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.log_issue uu____22027 uu____22028
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____22045 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____22045
         then
           let uu____22046 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____22047 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____22046
             uu____22047
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____22052 =
             let uu____22057 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____22057 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____22052 in
         let uu____22062 =
           let uu____22065 = singleton env prob in
           solve_and_commit env uu____22065
             (fun uu____22067  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____22062)
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
      fun uu____22096  ->
        match uu____22096 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22135 =
                 let uu____22140 =
                   let uu____22141 = FStar_Syntax_Print.univ_to_string u1 in
                   let uu____22142 = FStar_Syntax_Print.univ_to_string u2 in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____22141 uu____22142 in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____22140) in
               let uu____22143 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu____22135 uu____22143) in
            let equiv1 v1 v' =
              let uu____22151 =
                let uu____22156 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____22157 = FStar_Syntax_Subst.compress_univ v' in
                (uu____22156, uu____22157) in
              match uu____22151 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22176 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22206 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____22206 with
                      | FStar_Syntax_Syntax.U_unif uu____22213 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22242  ->
                                    match uu____22242 with
                                    | (u,v') ->
                                        let uu____22251 = equiv1 v1 v' in
                                        if uu____22251
                                        then
                                          let uu____22254 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____22254 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____22270 -> [])) in
            let uu____22275 =
              let wl =
                let uu___162_22279 = empty_worklist env in
                {
                  attempting = (uu___162_22279.attempting);
                  wl_deferred = (uu___162_22279.wl_deferred);
                  ctr = (uu___162_22279.ctr);
                  defer_ok = false;
                  smt_ok = (uu___162_22279.smt_ok);
                  tcenv = (uu___162_22279.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22297  ->
                      match uu____22297 with
                      | (lb,v1) ->
                          let uu____22304 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____22304 with
                           | USolved wl1 -> ()
                           | uu____22306 -> fail lb v1))) in
            let rec check_ineq uu____22314 =
              match uu____22314 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22323) -> true
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
                      uu____22346,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22348,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22359) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22366,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22374 -> false) in
            let uu____22379 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22394  ->
                      match uu____22394 with
                      | (u,v1) ->
                          let uu____22401 = check_ineq (u, v1) in
                          if uu____22401
                          then true
                          else
                            ((let uu____22404 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____22404
                              then
                                let uu____22405 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____22406 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____22405
                                  uu____22406
                              else ());
                             false))) in
            if uu____22379
            then ()
            else
              ((let uu____22410 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____22410
                then
                  ((let uu____22412 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22412);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22422 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22422))
                else ());
               (let uu____22432 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____22432))
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
      let fail uu____22480 =
        match uu____22480 with
        | (d,s) ->
            let msg = explain env d s in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
              (p_loc d) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____22494 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____22494
       then
         let uu____22495 = wl_to_string wl in
         let uu____22496 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22495 uu____22496
       else ());
      (let g1 =
         let uu____22511 = solve_and_commit env wl fail in
         match uu____22511 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___163_22524 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___163_22524.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___163_22524.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___163_22524.FStar_TypeChecker_Env.implicits)
             }
         | uu____22529 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___164_22533 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___164_22533.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___164_22533.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___164_22533.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____22559 = FStar_ST.op_Bang last_proof_ns in
    match uu____22559 with
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
            let uu___165_22662 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___165_22662.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___165_22662.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___165_22662.FStar_TypeChecker_Env.implicits)
            } in
          let uu____22663 =
            let uu____22664 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____22664 in
          if uu____22663
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22672 = FStar_TypeChecker_Env.get_range env in
                     let uu____22673 =
                       let uu____22674 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22674 in
                     FStar_Errors.diag uu____22672 uu____22673)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   if debug1
                   then
                     (let uu____22678 = FStar_TypeChecker_Env.get_range env in
                      let uu____22679 =
                        let uu____22680 =
                          FStar_Syntax_Print.term_to_string vc1 in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22680 in
                      FStar_Errors.diag uu____22678 uu____22679)
                   else ();
                   (let uu____22682 = check_trivial vc1 in
                    match uu____22682 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22689 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22690 =
                                let uu____22691 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22691 in
                              FStar_Errors.diag uu____22689 uu____22690)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22696 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22697 =
                                let uu____22698 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22698 in
                              FStar_Errors.diag uu____22696 uu____22697)
                           else ();
                           (let vcs =
                              let uu____22709 = FStar_Options.use_tactics () in
                              if uu____22709
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22728  ->
                                     (let uu____22730 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics" in
                                      FStar_All.pipe_left
                                        FStar_Pervasives.ignore uu____22730);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____22732 =
                                   let uu____22739 = FStar_Options.peek () in
                                   (env, vc2, uu____22739) in
                                 [uu____22732]) in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22773  ->
                                    match uu____22773 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal in
                                        let uu____22784 = check_trivial goal1 in
                                        (match uu____22784 with
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
                                                (let uu____22792 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22793 =
                                                   let uu____22794 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   let uu____22795 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1 in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22794 uu____22795 in
                                                 FStar_Errors.diag
                                                   uu____22792 uu____22793)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22798 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22799 =
                                                   let uu____22800 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22800 in
                                                 FStar_Errors.diag
                                                   uu____22798 uu____22799)
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
      let uu____22810 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____22810 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22816 = FStar_TypeChecker_Env.get_range env in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____22816
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____22823 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____22823 with
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
          let uu____22842 = FStar_Syntax_Unionfind.find u in
          match uu____22842 with
          | FStar_Pervasives_Native.None  -> true
          | uu____22845 -> false in
        let rec until_fixpoint acc implicits =
          let uu____22863 = acc in
          match uu____22863 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____22949 = hd1 in
                   (match uu____22949 with
                    | (uu____22962,env,u,tm,k,r) ->
                        let uu____22968 = unresolved u in
                        if uu____22968
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let env1 =
                             FStar_TypeChecker_Env.set_expected_typ env k in
                           let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env1 tm in
                           (let uu____22999 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck") in
                            if uu____22999
                            then
                              let uu____23000 =
                                FStar_Syntax_Print.uvar_to_string u in
                              let uu____23001 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____23002 =
                                FStar_Syntax_Print.term_to_string k in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____23000 uu____23001 uu____23002
                            else ());
                           (let env2 =
                              if forcelax
                              then
                                let uu___166_23005 = env1 in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___166_23005.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___166_23005.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___166_23005.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___166_23005.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___166_23005.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___166_23005.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___166_23005.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___166_23005.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___166_23005.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___166_23005.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___166_23005.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___166_23005.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___166_23005.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___166_23005.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___166_23005.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___166_23005.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___166_23005.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___166_23005.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax = true;
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___166_23005.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___166_23005.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___166_23005.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___166_23005.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___166_23005.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___166_23005.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___166_23005.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___166_23005.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___166_23005.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___166_23005.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___166_23005.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___166_23005.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___166_23005.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___166_23005.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.dep_graph =
                                    (uu___166_23005.FStar_TypeChecker_Env.dep_graph)
                                }
                              else env1 in
                            let g1 =
                              try
                                if must_total
                                then
                                  let uu____23014 =
                                    env2.FStar_TypeChecker_Env.type_of
                                      (let uu___169_23022 = env2 in
                                       {
                                         FStar_TypeChecker_Env.solver =
                                           (uu___169_23022.FStar_TypeChecker_Env.solver);
                                         FStar_TypeChecker_Env.range =
                                           (uu___169_23022.FStar_TypeChecker_Env.range);
                                         FStar_TypeChecker_Env.curmodule =
                                           (uu___169_23022.FStar_TypeChecker_Env.curmodule);
                                         FStar_TypeChecker_Env.gamma =
                                           (uu___169_23022.FStar_TypeChecker_Env.gamma);
                                         FStar_TypeChecker_Env.gamma_cache =
                                           (uu___169_23022.FStar_TypeChecker_Env.gamma_cache);
                                         FStar_TypeChecker_Env.modules =
                                           (uu___169_23022.FStar_TypeChecker_Env.modules);
                                         FStar_TypeChecker_Env.expected_typ =
                                           (uu___169_23022.FStar_TypeChecker_Env.expected_typ);
                                         FStar_TypeChecker_Env.sigtab =
                                           (uu___169_23022.FStar_TypeChecker_Env.sigtab);
                                         FStar_TypeChecker_Env.is_pattern =
                                           (uu___169_23022.FStar_TypeChecker_Env.is_pattern);
                                         FStar_TypeChecker_Env.instantiate_imp
                                           =
                                           (uu___169_23022.FStar_TypeChecker_Env.instantiate_imp);
                                         FStar_TypeChecker_Env.effects =
                                           (uu___169_23022.FStar_TypeChecker_Env.effects);
                                         FStar_TypeChecker_Env.generalize =
                                           (uu___169_23022.FStar_TypeChecker_Env.generalize);
                                         FStar_TypeChecker_Env.letrecs =
                                           (uu___169_23022.FStar_TypeChecker_Env.letrecs);
                                         FStar_TypeChecker_Env.top_level =
                                           (uu___169_23022.FStar_TypeChecker_Env.top_level);
                                         FStar_TypeChecker_Env.check_uvars =
                                           (uu___169_23022.FStar_TypeChecker_Env.check_uvars);
                                         FStar_TypeChecker_Env.use_eq =
                                           (uu___169_23022.FStar_TypeChecker_Env.use_eq);
                                         FStar_TypeChecker_Env.is_iface =
                                           (uu___169_23022.FStar_TypeChecker_Env.is_iface);
                                         FStar_TypeChecker_Env.admit =
                                           (uu___169_23022.FStar_TypeChecker_Env.admit);
                                         FStar_TypeChecker_Env.lax =
                                           (uu___169_23022.FStar_TypeChecker_Env.lax);
                                         FStar_TypeChecker_Env.lax_universes
                                           =
                                           (uu___169_23022.FStar_TypeChecker_Env.lax_universes);
                                         FStar_TypeChecker_Env.failhard =
                                           (uu___169_23022.FStar_TypeChecker_Env.failhard);
                                         FStar_TypeChecker_Env.nosynth =
                                           (uu___169_23022.FStar_TypeChecker_Env.nosynth);
                                         FStar_TypeChecker_Env.tc_term =
                                           (uu___169_23022.FStar_TypeChecker_Env.tc_term);
                                         FStar_TypeChecker_Env.type_of =
                                           (uu___169_23022.FStar_TypeChecker_Env.type_of);
                                         FStar_TypeChecker_Env.universe_of =
                                           (uu___169_23022.FStar_TypeChecker_Env.universe_of);
                                         FStar_TypeChecker_Env.use_bv_sorts =
                                           true;
                                         FStar_TypeChecker_Env.qname_and_index
                                           =
                                           (uu___169_23022.FStar_TypeChecker_Env.qname_and_index);
                                         FStar_TypeChecker_Env.proof_ns =
                                           (uu___169_23022.FStar_TypeChecker_Env.proof_ns);
                                         FStar_TypeChecker_Env.synth =
                                           (uu___169_23022.FStar_TypeChecker_Env.synth);
                                         FStar_TypeChecker_Env.is_native_tactic
                                           =
                                           (uu___169_23022.FStar_TypeChecker_Env.is_native_tactic);
                                         FStar_TypeChecker_Env.identifier_info
                                           =
                                           (uu___169_23022.FStar_TypeChecker_Env.identifier_info);
                                         FStar_TypeChecker_Env.tc_hooks =
                                           (uu___169_23022.FStar_TypeChecker_Env.tc_hooks);
                                         FStar_TypeChecker_Env.dsenv =
                                           (uu___169_23022.FStar_TypeChecker_Env.dsenv);
                                         FStar_TypeChecker_Env.dep_graph =
                                           (uu___169_23022.FStar_TypeChecker_Env.dep_graph)
                                       }) tm1 in
                                  match uu____23014 with
                                  | (uu____23023,uu____23024,g1) -> g1
                                else
                                  (let uu____23027 =
                                     env2.FStar_TypeChecker_Env.tc_term
                                       (let uu___170_23035 = env2 in
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (uu___170_23035.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (uu___170_23035.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (uu___170_23035.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (uu___170_23035.FStar_TypeChecker_Env.gamma);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (uu___170_23035.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (uu___170_23035.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (uu___170_23035.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (uu___170_23035.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.is_pattern =
                                            (uu___170_23035.FStar_TypeChecker_Env.is_pattern);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (uu___170_23035.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (uu___170_23035.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (uu___170_23035.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (uu___170_23035.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (uu___170_23035.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (uu___170_23035.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq =
                                            (uu___170_23035.FStar_TypeChecker_Env.use_eq);
                                          FStar_TypeChecker_Env.is_iface =
                                            (uu___170_23035.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (uu___170_23035.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax =
                                            (uu___170_23035.FStar_TypeChecker_Env.lax);
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (uu___170_23035.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.failhard =
                                            (uu___170_23035.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (uu___170_23035.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.tc_term =
                                            (uu___170_23035.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.type_of =
                                            (uu___170_23035.FStar_TypeChecker_Env.type_of);
                                          FStar_TypeChecker_Env.universe_of =
                                            (uu___170_23035.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            = true;
                                          FStar_TypeChecker_Env.qname_and_index
                                            =
                                            (uu___170_23035.FStar_TypeChecker_Env.qname_and_index);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (uu___170_23035.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth =
                                            (uu___170_23035.FStar_TypeChecker_Env.synth);
                                          FStar_TypeChecker_Env.is_native_tactic
                                            =
                                            (uu___170_23035.FStar_TypeChecker_Env.is_native_tactic);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (uu___170_23035.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (uu___170_23035.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (uu___170_23035.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.dep_graph =
                                            (uu___170_23035.FStar_TypeChecker_Env.dep_graph)
                                        }) tm1 in
                                   match uu____23027 with
                                   | (uu____23036,uu____23037,g1) -> g1)
                              with
                              | e ->
                                  ((let uu____23045 =
                                      let uu____23054 =
                                        let uu____23061 =
                                          let uu____23062 =
                                            FStar_Syntax_Print.uvar_to_string
                                              u in
                                          let uu____23063 =
                                            FStar_TypeChecker_Normalize.term_to_string
                                              env2 tm1 in
                                          FStar_Util.format2
                                            "Failed while checking implicit %s set to %s"
                                            uu____23062 uu____23063 in
                                        (FStar_Errors.Error_BadImplicit,
                                          uu____23061, r) in
                                      [uu____23054] in
                                    FStar_Errors.add_errors uu____23045);
                                   FStar_Exn.raise e) in
                            let g2 =
                              if env2.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___171_23077 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___171_23077.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___171_23077.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___171_23077.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____23080 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____23086  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env2 g2 true in
                              match uu____23080 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
        let uu___172_23114 = g in
        let uu____23115 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___172_23114.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___172_23114.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___172_23114.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____23115
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
        let uu____23169 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____23169 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23182 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____23182
      | (reason,uu____23184,uu____23185,e,t,r)::uu____23189 ->
          let uu____23216 =
            let uu____23221 =
              let uu____23222 = FStar_Syntax_Print.term_to_string t in
              let uu____23223 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format2
                "Failed to resolve implicit argument of type '%s' introduced in %s"
                uu____23222 uu____23223 in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____23221) in
          FStar_Errors.raise_error uu____23216 r
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___173_23230 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___173_23230.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___173_23230.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___173_23230.FStar_TypeChecker_Env.implicits)
      }
let discharge_guard_nosmt:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool =
  fun env  ->
    fun g  ->
      let uu____23253 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____23253 with
      | FStar_Pervasives_Native.Some uu____23258 -> true
      | FStar_Pervasives_Native.None  -> false
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23268 = try_teq false env t1 t2 in
        match uu____23268 with
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
        (let uu____23288 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____23288
         then
           let uu____23289 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____23290 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23289
             uu____23290
         else ());
        (let uu____23292 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
         match uu____23292 with
         | (prob,x) ->
             let g =
               let uu____23308 =
                 let uu____23311 = singleton' env prob true in
                 solve_and_commit env uu____23311
                   (fun uu____23313  -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____23308 in
             ((let uu____23323 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g) in
               if uu____23323
               then
                 let uu____23324 =
                   FStar_TypeChecker_Normalize.term_to_string env t1 in
                 let uu____23325 =
                   FStar_TypeChecker_Normalize.term_to_string env t2 in
                 let uu____23326 =
                   let uu____23327 = FStar_Util.must g in
                   guard_to_string env uu____23327 in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23324 uu____23325 uu____23326
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
        let uu____23355 = check_subtyping env t1 t2 in
        match uu____23355 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23374 =
              let uu____23375 = FStar_Syntax_Syntax.mk_binder x in
              abstract_guard uu____23375 g in
            FStar_Pervasives_Native.Some uu____23374
let get_subtyping_prop:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23387 = check_subtyping env t1 t2 in
        match uu____23387 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23406 =
              let uu____23407 =
                let uu____23408 = FStar_Syntax_Syntax.mk_binder x in
                [uu____23408] in
              close_guard env uu____23407 g in
            FStar_Pervasives_Native.Some uu____23406
let subtype_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23419 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____23419
         then
           let uu____23420 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____23421 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23420
             uu____23421
         else ());
        (let uu____23423 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
         match uu____23423 with
         | (prob,x) ->
             let g =
               let uu____23433 =
                 let uu____23436 = singleton' env prob false in
                 solve_and_commit env uu____23436
                   (fun uu____23438  -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____23433 in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23449 =
                      let uu____23450 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____23450] in
                    close_guard env uu____23449 g1 in
                  discharge_guard_nosmt env g2))