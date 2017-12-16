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
          let uu___253_91 = g in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___253_91.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___253_91.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___253_91.FStar_TypeChecker_Env.implicits)
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
          let uu___254_183 = g in
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
              (uu___254_183.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___254_183.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___254_183.FStar_TypeChecker_Env.implicits)
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
          let uu___255_226 = g in
          let uu____227 =
            let uu____228 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____228 in
          {
            FStar_TypeChecker_Env.guard_f = uu____227;
            FStar_TypeChecker_Env.deferred =
              (uu___255_226.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___255_226.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___255_226.FStar_TypeChecker_Env.implicits)
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
            let uu___256_352 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___256_352.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___256_352.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___256_352.FStar_TypeChecker_Env.implicits)
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
            let uu___257_384 = g in
            let uu____385 =
              let uu____386 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____386 in
            {
              FStar_TypeChecker_Env.guard_f = uu____385;
              FStar_TypeChecker_Env.deferred =
                (uu___257_384.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___257_384.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___257_384.FStar_TypeChecker_Env.implicits)
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
  fun uu___224_820  ->
    match uu___224_820 with
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
    fun uu___225_917  ->
      match uu___225_917 with
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
    fun uu___226_951  ->
      match uu___226_951 with
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
        let uu___258_1071 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___258_1071.wl_deferred);
          ctr = (uu___258_1071.ctr);
          defer_ok = (uu___258_1071.defer_ok);
          smt_ok;
          tcenv = (uu___258_1071.tcenv)
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
      let uu___259_1102 = empty_worklist env in
      let uu____1103 = FStar_List.map FStar_Pervasives_Native.snd g in
      {
        attempting = uu____1103;
        wl_deferred = (uu___259_1102.wl_deferred);
        ctr = (uu___259_1102.ctr);
        defer_ok = false;
        smt_ok = (uu___259_1102.smt_ok);
        tcenv = (uu___259_1102.tcenv)
      }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___260_1117 = wl in
        {
          attempting = (uu___260_1117.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___260_1117.ctr);
          defer_ok = (uu___260_1117.defer_ok);
          smt_ok = (uu___260_1117.smt_ok);
          tcenv = (uu___260_1117.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___261_1134 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___261_1134.wl_deferred);
        ctr = (uu___261_1134.ctr);
        defer_ok = (uu___261_1134.defer_ok);
        smt_ok = (uu___261_1134.smt_ok);
        tcenv = (uu___261_1134.tcenv)
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
  fun uu___227_1150  ->
    match uu___227_1150 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert:
  'Auu____1154 'Auu____1155 .
    ('Auu____1155,'Auu____1154) FStar_TypeChecker_Common.problem ->
      ('Auu____1155,'Auu____1154) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___262_1172 = p in
    {
      FStar_TypeChecker_Common.pid =
        (uu___262_1172.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___262_1172.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___262_1172.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___262_1172.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___262_1172.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___262_1172.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___262_1172.FStar_TypeChecker_Common.rank)
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
  fun uu___228_1201  ->
    match uu___228_1201 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.CProb _0_42)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___229_1225  ->
      match uu___229_1225 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___230_1228  ->
    match uu___230_1228 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___231_1241  ->
    match uu___231_1241 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___232_1256  ->
    match uu___232_1256 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___233_1271  ->
    match uu___233_1271 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___234_1288  ->
    match uu___234_1288 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___235_1305  ->
    match uu___235_1305 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___236_1318  ->
    match uu___236_1318 with
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
  'Auu____1446 'Auu____1447 .
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob ->
        'Auu____1447 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1447 ->
              'Auu____1446 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1447,'Auu____1446)
                    FStar_TypeChecker_Common.problem
  =
  fun scope  ->
    fun orig  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun reason  ->
                let uu____1484 = next_pid () in
                let uu____1485 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1484;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1485;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let new_problem:
  'Auu____1499 'Auu____1500 .
    FStar_TypeChecker_Env.env ->
      'Auu____1500 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1500 ->
            'Auu____1499 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1500,'Auu____1499)
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
                let uu____1538 = next_pid () in
                let uu____1539 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1538;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1539;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = [reason];
                  FStar_TypeChecker_Common.loc = loc;
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let problem_using_guard:
  'Auu____1552 'Auu____1553 .
    FStar_TypeChecker_Common.prob ->
      'Auu____1553 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1553 ->
            'Auu____1552 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____1553,'Auu____1552) FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____1586 = next_pid () in
              {
                FStar_TypeChecker_Common.pid = uu____1586;
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
  'Auu____1592 .
    worklist ->
      ('Auu____1592,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
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
        let uu____1642 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1642
        then
          let uu____1643 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1644 = prob_to_string env d in
          let uu____1645 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1643 uu____1644 uu____1645 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1651 -> failwith "impossible" in
           let uu____1652 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1666 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1667 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1666, uu____1667)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1673 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1674 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1673, uu____1674) in
           match uu____1652 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___237_1690  ->
            match uu___237_1690 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1702 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1704),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___238_1724  ->
           match uu___238_1724 with
           | UNIV uu____1727 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1733),t) ->
               let uu____1739 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1739
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
        (fun uu___239_1759  ->
           match uu___239_1759 with
           | UNIV (u',t) ->
               let uu____1764 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1764
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1768 -> FStar_Pervasives_Native.None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1775 =
        let uu____1776 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____1776 in
      FStar_Syntax_Subst.compress uu____1775
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1783 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1783
let norm_arg:
  'Auu____1787 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____1787) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1787)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____1808 = sn env (FStar_Pervasives_Native.fst t) in
      (uu____1808, (FStar_Pervasives_Native.snd t))
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
           (fun uu____1839  ->
              match uu____1839 with
              | (x,imp) ->
                  let uu____1850 =
                    let uu___263_1851 = x in
                    let uu____1852 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___263_1851.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___263_1851.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1852
                    } in
                  (uu____1850, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1867 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1867
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1871 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1871
        | uu____1874 -> u2 in
      let uu____1875 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1875
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
                (let uu____1987 = norm_refinement env t12 in
                 match uu____1987 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2004;
                     FStar_Syntax_Syntax.vars = uu____2005;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2031 =
                       let uu____2032 = FStar_Syntax_Print.term_to_string tt in
                       let uu____2033 = FStar_Syntax_Print.tag_of_term tt in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2032 uu____2033 in
                     failwith uu____2031)
          | FStar_Syntax_Syntax.Tm_uinst uu____2048 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____2085 =
                   let uu____2086 = FStar_Syntax_Subst.compress t1' in
                   uu____2086.FStar_Syntax_Syntax.n in
                 match uu____2085 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2103 -> aux true t1'
                 | uu____2110 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2125 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____2156 =
                   let uu____2157 = FStar_Syntax_Subst.compress t1' in
                   uu____2157.FStar_Syntax_Syntax.n in
                 match uu____2156 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2174 -> aux true t1'
                 | uu____2181 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2196 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____2241 =
                   let uu____2242 = FStar_Syntax_Subst.compress t1' in
                   uu____2242.FStar_Syntax_Syntax.n in
                 match uu____2241 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2259 -> aux true t1'
                 | uu____2266 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2281 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2296 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2311 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2326 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2341 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2368 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2399 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2430 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____2457 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____2494 ->
              let uu____2501 =
                let uu____2502 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2503 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2502 uu____2503 in
              failwith uu____2501
          | FStar_Syntax_Syntax.Tm_ascribed uu____2518 ->
              let uu____2545 =
                let uu____2546 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2547 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2546 uu____2547 in
              failwith uu____2545
          | FStar_Syntax_Syntax.Tm_delayed uu____2562 ->
              let uu____2587 =
                let uu____2588 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2589 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2588 uu____2589 in
              failwith uu____2587
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____2604 =
                let uu____2605 = FStar_Syntax_Print.term_to_string t12 in
                let uu____2606 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2605 uu____2606 in
              failwith uu____2604 in
        let uu____2621 = whnf env t1 in aux false uu____2621
let base_and_refinement:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t
let normalize_refinement:
  'Auu____2643 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____2643 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
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
      let uu____2666 = base_and_refinement env t in
      FStar_All.pipe_right uu____2666 FStar_Pervasives_Native.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____2700 = FStar_Syntax_Syntax.null_bv t in
    (uu____2700, FStar_Syntax_Util.t_true)
let as_refinement:
  'Auu____2706 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____2706 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____2727 = base_and_refinement_maybe_delta delta1 env t in
          match uu____2727 with
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
  fun uu____2806  ->
    match uu____2806 with
    | (t_base,refopt) ->
        let uu____2833 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
        (match uu____2833 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let uu____2865 =
      let uu____2868 =
        let uu____2871 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2894  ->
                  match uu____2894 with | (uu____2901,uu____2902,x) -> x)) in
        FStar_List.append wl.attempting uu____2871 in
      FStar_List.map (wl_prob_to_string wl) uu____2868 in
    FStar_All.pipe_right uu____2865 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2915 =
          let uu____2928 =
            let uu____2929 = FStar_Syntax_Subst.compress k in
            uu____2929.FStar_Syntax_Syntax.n in
          match uu____2928 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2982 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____2982)
              else
                (let uu____2996 = FStar_Syntax_Util.abs_formals t in
                 match uu____2996 with
                 | (ys',t1,uu____3019) ->
                     let uu____3024 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____3024))
          | uu____3065 ->
              let uu____3066 =
                let uu____3077 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____3077) in
              ((ys, t), uu____3066) in
        match uu____2915 with
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
                 let uu____3126 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____3126 c in
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
            let uu____3154 = p_guard prob in
            match uu____3154 with
            | (uu____3159,uv) ->
                ((let uu____3162 =
                    let uu____3163 = FStar_Syntax_Subst.compress uv in
                    uu____3163.FStar_Syntax_Syntax.n in
                  match uu____3162 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____3195 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____3195
                        then
                          let uu____3196 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____3197 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____3198 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3196
                            uu____3197 uu____3198
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____3200 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___264_3203 = wl in
                  {
                    attempting = (uu___264_3203.attempting);
                    wl_deferred = (uu___264_3203.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___264_3203.defer_ok);
                    smt_ok = (uu___264_3203.smt_ok);
                    tcenv = (uu___264_3203.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3218 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____3218
         then
           let uu____3219 = FStar_Util.string_of_int pid in
           let uu____3220 =
             let uu____3221 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____3221 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3219 uu____3220
         else ());
        commit sol;
        (let uu___265_3228 = wl in
         {
           attempting = (uu___265_3228.attempting);
           wl_deferred = (uu___265_3228.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___265_3228.defer_ok);
           smt_ok = (uu___265_3228.smt_ok);
           tcenv = (uu___265_3228.tcenv)
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
            | (uu____3266,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3278 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____3278 in
          (let uu____3284 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____3284
           then
             let uu____3285 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____3286 =
               let uu____3287 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____3287 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____3285 uu____3286
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
        let uu____3319 =
          let uu____3326 = FStar_Syntax_Free.uvars t in
          FStar_All.pipe_right uu____3326 FStar_Util.set_elements in
        FStar_All.pipe_right uu____3319
          (FStar_Util.for_some
             (fun uu____3362  ->
                match uu____3362 with
                | (uv,uu____3368) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
let occurs_check:
  'Auu____3375 'Auu____3376 .
    'Auu____3376 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3375)
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
            let uu____3408 = occurs wl uk t in Prims.op_Negation uu____3408 in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3415 =
                 let uu____3416 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk) in
                 let uu____3417 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3416 uu____3417 in
               FStar_Pervasives_Native.Some uu____3415) in
          (occurs_ok, msg)
let occurs_and_freevars_check:
  'Auu____3427 'Auu____3428 .
    'Auu____3428 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3427)
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
            let uu____3482 = occurs_check env wl uk t in
            match uu____3482 with
            | (occurs_ok,msg) ->
                let uu____3513 = FStar_Util.set_is_subset_of fvs_t fvs in
                (occurs_ok, uu____3513, (msg, fvs, fvs_t))
let intersect_vars:
  'Auu____3536 'Auu____3537 .
    (FStar_Syntax_Syntax.bv,'Auu____3537) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3536) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3536) FStar_Pervasives_Native.tuple2
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
      let uu____3621 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3675  ->
                fun uu____3676  ->
                  match (uu____3675, uu____3676) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____3757 =
                        let uu____3758 = FStar_Util.set_mem x v1_set in
                        FStar_All.pipe_left Prims.op_Negation uu____3758 in
                      if uu____3757
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                         let uu____3783 =
                           FStar_Util.set_is_subset_of fvs isect_set in
                         if uu____3783
                         then
                           let uu____3796 = FStar_Util.set_add x isect_set in
                           (((x, imp) :: isect), uu____3796)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names)) in
      match uu____3621 with | (isect,uu____3837) -> FStar_List.rev isect
let binders_eq:
  'Auu____3862 'Auu____3863 .
    (FStar_Syntax_Syntax.bv,'Auu____3863) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3862) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____3918  ->
              fun uu____3919  ->
                match (uu____3918, uu____3919) with
                | ((a,uu____3937),(b,uu____3939)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt:
  'Auu____3953 'Auu____3954 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____3954) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____3953)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____3953)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4005 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4019  ->
                      match uu____4019 with
                      | (b,uu____4025) -> FStar_Syntax_Syntax.bv_eq a b)) in
            if uu____4005
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4041 -> FStar_Pervasives_Native.None
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
            let uu____4114 = pat_var_opt env seen hd1 in
            (match uu____4114 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4128 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____4128
                   then
                     let uu____4129 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4129
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4147 =
      let uu____4148 = FStar_Syntax_Subst.compress t in
      uu____4148.FStar_Syntax_Syntax.n in
    match uu____4147 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4151 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4168;
           FStar_Syntax_Syntax.pos = uu____4169;
           FStar_Syntax_Syntax.vars = uu____4170;_},uu____4171)
        -> true
    | uu____4208 -> false
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
           FStar_Syntax_Syntax.pos = uu____4332;
           FStar_Syntax_Syntax.vars = uu____4333;_},args)
        -> (t, uv, k, args)
    | uu____4401 -> failwith "Not a flex-uvar"
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
      let uu____4478 = destruct_flex_t t in
      match uu____4478 with
      | (t1,uv,k,args) ->
          let uu____4593 = pat_vars env [] args in
          (match uu____4593 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4691 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch[@@deriving show]
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____4772 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____4807 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____4811 -> false
let head_match: match_result -> match_result =
  fun uu___240_4814  ->
    match uu___240_4814 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____4829 -> HeadMatch
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____4838 ->
          let uu____4839 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____4839 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____4850 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____4869 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____4878 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____4905 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____4906 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____4907 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____4924 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____4937 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____4961) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____4967,uu____4968) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5010) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5031;
             FStar_Syntax_Syntax.index = uu____5032;
             FStar_Syntax_Syntax.sort = t2;_},uu____5034)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5041 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5042 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5043 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5056 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5074 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____5074
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
            let uu____5095 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____5095
            then FullMatch
            else
              (let uu____5097 =
                 let uu____5106 =
                   let uu____5109 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____5109 in
                 let uu____5110 =
                   let uu____5113 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____5113 in
                 (uu____5106, uu____5110) in
               MisMatch uu____5097)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5119),FStar_Syntax_Syntax.Tm_uinst (g,uu____5121)) ->
            let uu____5130 = head_matches env f g in
            FStar_All.pipe_right uu____5130 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5133 = FStar_Const.eq_const c d in
            if uu____5133
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5140),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5142)) ->
            let uu____5191 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____5191
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5198),FStar_Syntax_Syntax.Tm_refine (y,uu____5200)) ->
            let uu____5209 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5209 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5211),uu____5212) ->
            let uu____5217 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____5217 head_match
        | (uu____5218,FStar_Syntax_Syntax.Tm_refine (x,uu____5220)) ->
            let uu____5225 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5225 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5226,FStar_Syntax_Syntax.Tm_type
           uu____5227) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5228,FStar_Syntax_Syntax.Tm_arrow uu____5229) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5255),FStar_Syntax_Syntax.Tm_app (head',uu____5257))
            ->
            let uu____5298 = head_matches env head1 head' in
            FStar_All.pipe_right uu____5298 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5300),uu____5301) ->
            let uu____5322 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____5322 head_match
        | (uu____5323,FStar_Syntax_Syntax.Tm_app (head1,uu____5325)) ->
            let uu____5346 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____5346 head_match
        | uu____5347 ->
            let uu____5352 =
              let uu____5361 = delta_depth_of_term env t11 in
              let uu____5364 = delta_depth_of_term env t21 in
              (uu____5361, uu____5364) in
            MisMatch uu____5352
let head_matches_delta:
  'Auu____5376 .
    FStar_TypeChecker_Env.env ->
      'Auu____5376 ->
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
            let uu____5409 = FStar_Syntax_Util.head_and_args t in
            match uu____5409 with
            | (head1,uu____5427) ->
                let uu____5448 =
                  let uu____5449 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5449.FStar_Syntax_Syntax.n in
                (match uu____5448 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5455 =
                       let uu____5456 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_All.pipe_right uu____5456 FStar_Option.isSome in
                     if uu____5455
                     then
                       let uu____5475 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t in
                       FStar_All.pipe_right uu____5475
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                     else FStar_Pervasives_Native.None
                 | uu____5479 -> FStar_Pervasives_Native.None) in
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
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5582)
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5600 =
                     let uu____5609 = maybe_inline t11 in
                     let uu____5612 = maybe_inline t21 in
                     (uu____5609, uu____5612) in
                   match uu____5600 with
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
                (uu____5649,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5667 =
                     let uu____5676 = maybe_inline t11 in
                     let uu____5679 = maybe_inline t21 in
                     (uu____5676, uu____5679) in
                   match uu____5667 with
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
                let uu____5722 = FStar_TypeChecker_Common.decr_delta_depth d1 in
                (match uu____5722 with
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
                let uu____5745 =
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
                (match uu____5745 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____5769 -> fail r
            | uu____5778 -> success n_delta r t11 t21 in
          aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp[@@deriving show]
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____5811 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____5847 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list[@@deriving show]
let tc_to_string: tc -> Prims.string =
  fun uu___241_5859  ->
    match uu___241_5859 with
    | T (t,uu____5861) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____5877 = FStar_Syntax_Util.type_u () in
      match uu____5877 with
      | (t,uu____5883) ->
          let uu____5884 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____5884
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____5895 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____5895 FStar_Pervasives_Native.fst
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
        let uu____5959 = head_matches env t1 t' in
        match uu____5959 with
        | MisMatch uu____5960 -> false
        | uu____5969 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6065,imp),T (t2,uu____6068)) -> (t2, imp)
                     | uu____6087 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6154  ->
                    match uu____6154 with
                    | (t2,uu____6168) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6211 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6211 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6286))::tcs2) ->
                       aux
                         (((let uu___266_6321 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___266_6321.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___266_6321.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6339 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___242_6392 =
                 match uu___242_6392 with
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
               let uu____6509 = decompose1 [] bs1 in
               (rebuild, matches, uu____6509))
      | uu____6558 ->
          let rebuild uu___243_6564 =
            match uu___243_6564 with
            | [] -> t1
            | uu____6567 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___244_6598  ->
    match uu___244_6598 with
    | T (t,uu____6600) -> t
    | uu____6609 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___245_6612  ->
    match uu___245_6612 with
    | T (t,uu____6614) -> FStar_Syntax_Syntax.as_arg t
    | uu____6623 -> failwith "Impossible"
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
              | (uu____6729,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____6754 = new_uvar r scope1 k in
                  (match uu____6754 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____6772 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____6789 =
                         let uu____6790 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____6790 in
                       ((T (gi_xs, mk_kind)), uu____6789))
              | (uu____6803,uu____6804,C uu____6805) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____6952 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____6969;
                         FStar_Syntax_Syntax.vars = uu____6970;_})
                        ->
                        let uu____6993 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____6993 with
                         | (T (gi_xs,uu____7017),prob) ->
                             let uu____7027 =
                               let uu____7028 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____7028 in
                             (uu____7027, [prob])
                         | uu____7031 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7046;
                         FStar_Syntax_Syntax.vars = uu____7047;_})
                        ->
                        let uu____7070 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7070 with
                         | (T (gi_xs,uu____7094),prob) ->
                             let uu____7104 =
                               let uu____7105 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____7105 in
                             (uu____7104, [prob])
                         | uu____7108 -> failwith "impossible")
                    | (uu____7119,uu____7120,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7122;
                         FStar_Syntax_Syntax.vars = uu____7123;_})
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
                        let uu____7254 =
                          let uu____7263 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____7263 FStar_List.unzip in
                        (match uu____7254 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7317 =
                                 let uu____7318 =
                                   let uu____7321 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____7321 un_T in
                                 let uu____7322 =
                                   let uu____7331 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____7331
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7318;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7322;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7317 in
                             ((C gi_xs), sub_probs))
                    | uu____7340 ->
                        let uu____7353 = sub_prob scope1 args q in
                        (match uu____7353 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____6952 with
                   | (tc,probs) ->
                       let uu____7384 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7447,uu____7448),T
                            (t,uu____7450)) ->
                             let b1 =
                               ((let uu___267_7487 = b in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___267_7487.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___267_7487.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp) in
                             let uu____7488 =
                               let uu____7495 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1 in
                               uu____7495 :: args in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7488)
                         | uu____7530 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____7384 with
                        | (bopt,scope2,args1) ->
                            let uu____7614 = aux scope2 args1 qs2 in
                            (match uu____7614 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____7651 =
                                         let uu____7654 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____7654 in
                                       FStar_Syntax_Util.mk_conj_l uu____7651
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____7677 =
                                         let uu____7680 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____7681 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____7680 :: uu____7681 in
                                       FStar_Syntax_Util.mk_conj_l uu____7677 in
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
  'Auu____7749 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____7749)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____7749)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___268_7770 = p in
      let uu____7775 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____7776 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___268_7770.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7775;
        FStar_TypeChecker_Common.relation =
          (uu___268_7770.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7776;
        FStar_TypeChecker_Common.element =
          (uu___268_7770.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___268_7770.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___268_7770.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___268_7770.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___268_7770.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___268_7770.FStar_TypeChecker_Common.rank)
      }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7788 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____7788
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____7797 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____7817 = compress_prob wl pr in
        FStar_All.pipe_right uu____7817 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7827 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____7827 with
           | (lh,uu____7847) ->
               let uu____7868 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____7868 with
                | (rh,uu____7888) ->
                    let uu____7909 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7926,FStar_Syntax_Syntax.Tm_uvar uu____7927)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7964,uu____7965)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____7986,FStar_Syntax_Syntax.Tm_uvar uu____7987)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8008,uu____8009)
                          ->
                          let uu____8026 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____8026 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8075 ->
                                    let rank =
                                      let uu____8083 = is_top_level_prob prob in
                                      if uu____8083
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____8085 =
                                      let uu___269_8090 = tp in
                                      let uu____8095 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___269_8090.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___269_8090.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___269_8090.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8095;
                                        FStar_TypeChecker_Common.element =
                                          (uu___269_8090.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___269_8090.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___269_8090.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___269_8090.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___269_8090.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___269_8090.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____8085)))
                      | (uu____8106,FStar_Syntax_Syntax.Tm_uvar uu____8107)
                          ->
                          let uu____8124 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____8124 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8173 ->
                                    let uu____8180 =
                                      let uu___270_8187 = tp in
                                      let uu____8192 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___270_8187.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8192;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___270_8187.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___270_8187.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___270_8187.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___270_8187.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___270_8187.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___270_8187.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___270_8187.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___270_8187.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____8180)))
                      | (uu____8209,uu____8210) -> (rigid_rigid, tp) in
                    (match uu____7909 with
                     | (rank,tp1) ->
                         let uu____8229 =
                           FStar_All.pipe_right
                             (let uu___271_8235 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___271_8235.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___271_8235.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___271_8235.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___271_8235.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___271_8235.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___271_8235.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___271_8235.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___271_8235.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___271_8235.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50) in
                         (rank, uu____8229))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8245 =
            FStar_All.pipe_right
              (let uu___272_8251 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___272_8251.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___272_8251.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___272_8251.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___272_8251.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___272_8251.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___272_8251.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___272_8251.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___272_8251.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___272_8251.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51) in
          (rigid_rigid, uu____8245)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____8306 probs =
      match uu____8306 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8359 = rank wl hd1 in
               (match uu____8359 with
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
    match projectee with | UDeferred _0 -> true | uu____8466 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8478 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8490 -> false
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
                        let uu____8530 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____8530 with
                        | (k,uu____8536) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8546 -> false)))
            | uu____8547 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____8598 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____8598 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____8601 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____8611 =
                     let uu____8612 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____8613 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____8612
                       uu____8613 in
                   UFailed uu____8611)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8633 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8633 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8655 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8655 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____8658 ->
                let uu____8663 =
                  let uu____8664 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____8665 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8664
                    uu____8665 msg in
                UFailed uu____8663 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8666,uu____8667) ->
              let uu____8668 =
                let uu____8669 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8670 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8669 uu____8670 in
              failwith uu____8668
          | (FStar_Syntax_Syntax.U_unknown ,uu____8671) ->
              let uu____8672 =
                let uu____8673 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8674 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8673 uu____8674 in
              failwith uu____8672
          | (uu____8675,FStar_Syntax_Syntax.U_bvar uu____8676) ->
              let uu____8677 =
                let uu____8678 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8679 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8678 uu____8679 in
              failwith uu____8677
          | (uu____8680,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8681 =
                let uu____8682 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8683 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8682 uu____8683 in
              failwith uu____8681
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8707 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____8707
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____8729 = occurs_univ v1 u3 in
              if uu____8729
              then
                let uu____8730 =
                  let uu____8731 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____8732 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8731 uu____8732 in
                try_umax_components u11 u21 uu____8730
              else
                (let uu____8734 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____8734)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____8754 = occurs_univ v1 u3 in
              if uu____8754
              then
                let uu____8755 =
                  let uu____8756 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____8757 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8756 uu____8757 in
                try_umax_components u11 u21 uu____8755
              else
                (let uu____8759 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____8759)
          | (FStar_Syntax_Syntax.U_max uu____8768,uu____8769) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____8775 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____8775
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8777,FStar_Syntax_Syntax.U_max uu____8778) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____8784 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____8784
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8786,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8787,FStar_Syntax_Syntax.U_name
             uu____8788) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8789) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8790) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8791,FStar_Syntax_Syntax.U_succ
             uu____8792) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8793,FStar_Syntax_Syntax.U_zero
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
      let uu____8879 = bc1 in
      match uu____8879 with
      | (bs1,mk_cod1) ->
          let uu____8920 = bc2 in
          (match uu____8920 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____8990 = FStar_Util.first_N n1 bs in
                 match uu____8990 with
                 | (bs3,rest) ->
                     let uu____9015 = mk_cod rest in (bs3, uu____9015) in
               let l1 = FStar_List.length bs1 in
               let l2 = FStar_List.length bs2 in
               if l1 = l2
               then
                 let uu____9044 =
                   let uu____9051 = mk_cod1 [] in (bs1, uu____9051) in
                 let uu____9054 =
                   let uu____9061 = mk_cod2 [] in (bs2, uu____9061) in
                 (uu____9044, uu____9054)
               else
                 if l1 > l2
                 then
                   (let uu____9103 = curry l2 bs1 mk_cod1 in
                    let uu____9116 =
                      let uu____9123 = mk_cod2 [] in (bs2, uu____9123) in
                    (uu____9103, uu____9116))
                 else
                   (let uu____9139 =
                      let uu____9146 = mk_cod1 [] in (bs1, uu____9146) in
                    let uu____9149 = curry l1 bs2 mk_cod2 in
                    (uu____9139, uu____9149)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____9270 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9270
       then
         let uu____9271 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9271
       else ());
      (let uu____9273 = next_prob probs in
       match uu____9273 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___273_9294 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___273_9294.wl_deferred);
               ctr = (uu___273_9294.ctr);
               defer_ok = (uu___273_9294.defer_ok);
               smt_ok = (uu___273_9294.smt_ok);
               tcenv = (uu___273_9294.tcenv)
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
                  let uu____9305 = solve_flex_rigid_join env tp probs1 in
                  (match uu____9305 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9310 = solve_rigid_flex_meet env tp probs1 in
                     match uu____9310 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9315,uu____9316) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9333 ->
                let uu____9342 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9401  ->
                          match uu____9401 with
                          | (c,uu____9409,uu____9410) -> c < probs.ctr)) in
                (match uu____9342 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9451 =
                            FStar_List.map
                              (fun uu____9466  ->
                                 match uu____9466 with
                                 | (uu____9477,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____9451
                      | uu____9480 ->
                          let uu____9489 =
                            let uu___274_9490 = probs in
                            let uu____9491 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9512  ->
                                      match uu____9512 with
                                      | (uu____9519,uu____9520,y) -> y)) in
                            {
                              attempting = uu____9491;
                              wl_deferred = rest;
                              ctr = (uu___274_9490.ctr);
                              defer_ok = (uu___274_9490.defer_ok);
                              smt_ok = (uu___274_9490.smt_ok);
                              tcenv = (uu___274_9490.tcenv)
                            } in
                          solve env uu____9489))))
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
            let uu____9527 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____9527 with
            | USolved wl1 ->
                let uu____9529 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____9529
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
                  let uu____9575 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____9575 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9578 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9590;
                  FStar_Syntax_Syntax.vars = uu____9591;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9594;
                  FStar_Syntax_Syntax.vars = uu____9595;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9609,uu____9610) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9617,FStar_Syntax_Syntax.Tm_uinst uu____9618) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9625 -> USolved wl
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
            ((let uu____9635 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____9635
              then
                let uu____9636 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____9636 msg
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
        (let uu____9645 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____9645
         then
           let uu____9646 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____9646
         else ());
        (let uu____9648 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____9648 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____9710 = head_matches_delta env () t1 t2 in
               match uu____9710 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____9751 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____9800 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____9815 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____9816 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____9815, uu____9816)
                          | FStar_Pervasives_Native.None  ->
                              let uu____9821 = FStar_Syntax_Subst.compress t1 in
                              let uu____9822 = FStar_Syntax_Subst.compress t2 in
                              (uu____9821, uu____9822) in
                        (match uu____9800 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____9848 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____9848 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____9879 =
                                    let uu____9888 =
                                      let uu____9891 =
                                        let uu____9894 =
                                          let uu____9895 =
                                            let uu____9902 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____9902) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____9895 in
                                        FStar_Syntax_Syntax.mk uu____9894 in
                                      uu____9891 FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____9910 =
                                      let uu____9913 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____9913] in
                                    (uu____9888, uu____9910) in
                                  FStar_Pervasives_Native.Some uu____9879
                              | (uu____9926,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____9928)) ->
                                  let uu____9933 =
                                    let uu____9940 =
                                      let uu____9943 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____9943] in
                                    (t11, uu____9940) in
                                  FStar_Pervasives_Native.Some uu____9933
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____9953),uu____9954) ->
                                  let uu____9959 =
                                    let uu____9966 =
                                      let uu____9969 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____9969] in
                                    (t21, uu____9966) in
                                  FStar_Pervasives_Native.Some uu____9959
                              | uu____9978 ->
                                  let uu____9983 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____9983 with
                                   | (head1,uu____10007) ->
                                       let uu____10028 =
                                         let uu____10029 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____10029.FStar_Syntax_Syntax.n in
                                       (match uu____10028 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10040;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10042;_}
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
                                        | uu____10049 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10062) ->
                  let uu____10087 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___246_10113  ->
                            match uu___246_10113 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10120 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____10120 with
                                      | (u',uu____10136) ->
                                          let uu____10157 =
                                            let uu____10158 = whnf env u' in
                                            uu____10158.FStar_Syntax_Syntax.n in
                                          (match uu____10157 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10162) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10187 -> false))
                                 | uu____10188 -> false)
                            | uu____10191 -> false)) in
                  (match uu____10087 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10225 tps =
                         match uu____10225 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10273 =
                                    let uu____10282 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____10282 in
                                  (match uu____10273 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10317 -> FStar_Pervasives_Native.None) in
                       let uu____10326 =
                         let uu____10335 =
                           let uu____10342 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____10342, []) in
                         make_lower_bound uu____10335 lower_bounds in
                       (match uu____10326 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10354 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10354
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
                            ((let uu____10374 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10374
                              then
                                let wl' =
                                  let uu___275_10376 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___275_10376.wl_deferred);
                                    ctr = (uu___275_10376.ctr);
                                    defer_ok = (uu___275_10376.defer_ok);
                                    smt_ok = (uu___275_10376.smt_ok);
                                    tcenv = (uu___275_10376.tcenv)
                                  } in
                                let uu____10377 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10377
                              else ());
                             (let uu____10379 =
                                solve_t env eq_prob
                                  (let uu___276_10381 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___276_10381.wl_deferred);
                                     ctr = (uu___276_10381.ctr);
                                     defer_ok = (uu___276_10381.defer_ok);
                                     smt_ok = (uu___276_10381.smt_ok);
                                     tcenv = (uu___276_10381.tcenv)
                                   }) in
                              match uu____10379 with
                              | Success uu____10384 ->
                                  let wl1 =
                                    let uu___277_10386 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___277_10386.wl_deferred);
                                      ctr = (uu___277_10386.ctr);
                                      defer_ok = (uu___277_10386.defer_ok);
                                      smt_ok = (uu___277_10386.smt_ok);
                                      tcenv = (uu___277_10386.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____10388 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10393 -> FStar_Pervasives_Native.None))))
              | uu____10394 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10403 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10403
         then
           let uu____10404 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10404
         else ());
        (let uu____10406 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____10406 with
         | (u,args) ->
             let uu____10445 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____10445 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____10486 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____10486 with
                    | (h1,args1) ->
                        let uu____10527 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____10527 with
                         | (h2,uu____10547) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____10574 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____10574
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____10592 =
                                          let uu____10595 =
                                            let uu____10596 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____10596 in
                                          [uu____10595] in
                                        FStar_Pervasives_Native.Some
                                          uu____10592))
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
                                       (let uu____10629 =
                                          let uu____10632 =
                                            let uu____10633 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____10633 in
                                          [uu____10632] in
                                        FStar_Pervasives_Native.Some
                                          uu____10629))
                                  else FStar_Pervasives_Native.None
                              | uu____10647 -> FStar_Pervasives_Native.None)) in
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
                             let uu____10737 =
                               let uu____10746 =
                                 let uu____10749 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____10749 in
                               (uu____10746, m1) in
                             FStar_Pervasives_Native.Some uu____10737)
                    | (uu____10762,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____10764)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____10812),uu____10813) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____10860 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10913) ->
                       let uu____10938 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___247_10964  ->
                                 match uu___247_10964 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____10971 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____10971 with
                                           | (u',uu____10987) ->
                                               let uu____11008 =
                                                 let uu____11009 =
                                                   whnf env u' in
                                                 uu____11009.FStar_Syntax_Syntax.n in
                                               (match uu____11008 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11013) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11038 -> false))
                                      | uu____11039 -> false)
                                 | uu____11042 -> false)) in
                       (match uu____10938 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11080 tps =
                              match uu____11080 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11142 =
                                         let uu____11153 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____11153 in
                                       (match uu____11142 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11204 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____11215 =
                              let uu____11226 =
                                let uu____11235 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____11235, []) in
                              make_upper_bound uu____11226 upper_bounds in
                            (match uu____11215 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11249 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11249
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
                                 ((let uu____11275 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11275
                                   then
                                     let wl' =
                                       let uu___278_11277 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___278_11277.wl_deferred);
                                         ctr = (uu___278_11277.ctr);
                                         defer_ok = (uu___278_11277.defer_ok);
                                         smt_ok = (uu___278_11277.smt_ok);
                                         tcenv = (uu___278_11277.tcenv)
                                       } in
                                     let uu____11278 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11278
                                   else ());
                                  (let uu____11280 =
                                     solve_t env eq_prob
                                       (let uu___279_11282 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___279_11282.wl_deferred);
                                          ctr = (uu___279_11282.ctr);
                                          defer_ok =
                                            (uu___279_11282.defer_ok);
                                          smt_ok = (uu___279_11282.smt_ok);
                                          tcenv = (uu___279_11282.tcenv)
                                        }) in
                                   match uu____11280 with
                                   | Success uu____11285 ->
                                       let wl1 =
                                         let uu___280_11287 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___280_11287.wl_deferred);
                                           ctr = (uu___280_11287.ctr);
                                           defer_ok =
                                             (uu___280_11287.defer_ok);
                                           smt_ok = (uu___280_11287.smt_ok);
                                           tcenv = (uu___280_11287.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____11289 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11294 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11295 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____11370 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____11370
                      then
                        let uu____11371 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11371
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___281_11425 = hd1 in
                      let uu____11426 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___281_11425.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___281_11425.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11426
                      } in
                    let hd21 =
                      let uu___282_11430 = hd2 in
                      let uu____11431 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___282_11430.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___282_11430.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11431
                      } in
                    let prob =
                      let uu____11435 =
                        let uu____11440 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11440 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____11435 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____11451 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11451 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____11455 =
                      aux (FStar_List.append scope [(hd12, imp)]) env2 subst2
                        xs1 ys1 in
                    (match uu____11455 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11493 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____11498 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____11493 uu____11498 in
                         ((let uu____11508 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____11508
                           then
                             let uu____11509 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____11510 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11509 uu____11510
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11533 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____11543 = aux scope env [] bs1 bs2 in
              match uu____11543 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____11567 = compress_tprob wl problem in
        solve_t' env uu____11567 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____11600 = head_matches_delta env1 wl1 t1 t2 in
          match uu____11600 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____11631,uu____11632) ->
                   let rec may_relate head3 =
                     let uu____11657 =
                       let uu____11658 = FStar_Syntax_Subst.compress head3 in
                       uu____11658.FStar_Syntax_Syntax.n in
                     match uu____11657 with
                     | FStar_Syntax_Syntax.Tm_name uu____11661 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____11662 -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____11685;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_equational ;
                           FStar_Syntax_Syntax.fv_qual = uu____11686;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____11689;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_abstract uu____11690;
                           FStar_Syntax_Syntax.fv_qual = uu____11691;_}
                         ->
                         problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____11695,uu____11696) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____11738) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____11744) ->
                         may_relate t
                     | uu____11749 -> false in
                   let uu____11750 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____11750
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
                                let uu____11767 =
                                  let uu____11768 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____11768 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____11767 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____11770 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____11770
                   else
                     (let uu____11772 =
                        let uu____11773 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____11774 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____11773 uu____11774 in
                      giveup env1 uu____11772 orig)
               | (uu____11775,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___283_11789 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___283_11789.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___283_11789.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___283_11789.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___283_11789.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___283_11789.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___283_11789.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___283_11789.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___283_11789.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____11790,FStar_Pervasives_Native.None ) ->
                   ((let uu____11802 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____11802
                     then
                       let uu____11803 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____11804 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____11805 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____11806 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____11803
                         uu____11804 uu____11805 uu____11806
                     else ());
                    (let uu____11808 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____11808 with
                     | (head11,args1) ->
                         let uu____11845 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____11845 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____11899 =
                                  let uu____11900 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____11901 = args_to_string args1 in
                                  let uu____11902 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____11903 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____11900 uu____11901 uu____11902
                                    uu____11903 in
                                giveup env1 uu____11899 orig
                              else
                                (let uu____11905 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____11911 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____11911 = FStar_Syntax_Util.Equal) in
                                 if uu____11905
                                 then
                                   let uu____11912 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____11912 with
                                   | USolved wl2 ->
                                       let uu____11914 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____11914
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____11918 =
                                      base_and_refinement env1 t1 in
                                    match uu____11918 with
                                    | (base1,refinement1) ->
                                        let uu____11943 =
                                          base_and_refinement env1 t2 in
                                        (match uu____11943 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____12000 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____12000 with
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
                                                           (fun uu____12022 
                                                              ->
                                                              fun uu____12023
                                                                 ->
                                                                match 
                                                                  (uu____12022,
                                                                    uu____12023)
                                                                with
                                                                | ((a,uu____12041),
                                                                   (a',uu____12043))
                                                                    ->
                                                                    let uu____12052
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
                                                                    uu____12052)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____12062 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____12062 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____12068 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___284_12104 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___284_12104.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___284_12104.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___284_12104.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___284_12104.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___284_12104.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___284_12104.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___284_12104.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___284_12104.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let force_quasi_pattern xs_opt uu____12137 =
          match uu____12137 with
          | (t,u,k,args) ->
              let debug1 f =
                let uu____12179 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel") in
                if uu____12179 then f () else () in
              let rec aux pat_args pat_args_set pattern_vars pattern_var_set
                seen_formals formals res_t args1 =
                debug1
                  (fun uu____12275  ->
                     let uu____12276 =
                       FStar_Syntax_Print.binders_to_string ", " pat_args in
                     FStar_Util.print1 "pat_args so far: {%s}\n" uu____12276);
                (match (formals, args1) with
                 | ([],[]) ->
                     let pat_args1 =
                       FStar_All.pipe_right (FStar_List.rev pat_args)
                         (FStar_List.map
                            (fun uu____12344  ->
                               match uu____12344 with
                               | (x,imp) ->
                                   let uu____12355 =
                                     FStar_Syntax_Syntax.bv_to_name x in
                                   (uu____12355, imp))) in
                     let pattern_vars1 = FStar_List.rev pattern_vars in
                     let kk =
                       let uu____12368 = FStar_Syntax_Util.type_u () in
                       match uu____12368 with
                       | (t1,uu____12374) ->
                           let uu____12375 =
                             new_uvar t1.FStar_Syntax_Syntax.pos
                               pattern_vars1 t1 in
                           FStar_Pervasives_Native.fst uu____12375 in
                     let uu____12380 =
                       new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk in
                     (match uu____12380 with
                      | (t',tm_u1) ->
                          let uu____12393 = destruct_flex_t t' in
                          (match uu____12393 with
                           | (uu____12430,u1,k1,uu____12433) ->
                               let all_formals = FStar_List.rev seen_formals in
                               let k2 =
                                 let uu____12492 =
                                   FStar_Syntax_Syntax.mk_Total res_t in
                                 FStar_Syntax_Util.arrow all_formals
                                   uu____12492 in
                               let sol =
                                 let uu____12496 =
                                   let uu____12505 = u_abs k2 all_formals t' in
                                   ((u, k2), uu____12505) in
                                 TERM uu____12496 in
                               let t_app =
                                 FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                   pat_args1 FStar_Pervasives_Native.None
                                   t.FStar_Syntax_Syntax.pos in
                               FStar_Pervasives_Native.Some
                                 (sol, (t_app, u1, k1, pat_args1))))
                 | (formal::formals1,hd1::tl1) ->
                     (debug1
                        (fun uu____12640  ->
                           let uu____12641 =
                             FStar_Syntax_Print.binder_to_string formal in
                           let uu____12642 =
                             FStar_Syntax_Print.args_to_string [hd1] in
                           FStar_Util.print2
                             "force_quasi_pattern (case 2): formal=%s, hd=%s\n"
                             uu____12641 uu____12642);
                      (let uu____12655 = pat_var_opt env pat_args hd1 in
                       match uu____12655 with
                       | FStar_Pervasives_Native.None  ->
                           (debug1
                              (fun uu____12675  ->
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
                                      (fun uu____12718  ->
                                         match uu____12718 with
                                         | (x,uu____12724) ->
                                             FStar_Syntax_Syntax.bv_eq x
                                               (FStar_Pervasives_Native.fst y))) in
                           if Prims.op_Negation maybe_pat
                           then
                             aux pat_args pat_args_set pattern_vars
                               pattern_var_set (formal :: seen_formals)
                               formals1 res_t tl1
                           else
                             (debug1
                                (fun uu____12739  ->
                                   let uu____12740 =
                                     FStar_Syntax_Print.args_to_string [hd1] in
                                   let uu____12753 =
                                     FStar_Syntax_Print.binder_to_string y in
                                   FStar_Util.print2
                                     "%s (var = %s) maybe pat\n" uu____12740
                                     uu____12753);
                              (let fvs =
                                 FStar_Syntax_Free.names
                                   (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort in
                               let uu____12757 =
                                 let uu____12758 =
                                   FStar_Util.set_is_subset_of fvs
                                     pat_args_set in
                                 Prims.op_Negation uu____12758 in
                               if uu____12757
                               then
                                 (debug1
                                    (fun uu____12770  ->
                                       let uu____12771 =
                                         let uu____12774 =
                                           FStar_Syntax_Print.args_to_string
                                             [hd1] in
                                         let uu____12787 =
                                           let uu____12790 =
                                             FStar_Syntax_Print.binder_to_string
                                               y in
                                           let uu____12791 =
                                             let uu____12794 =
                                               FStar_Syntax_Print.term_to_string
                                                 (FStar_Pervasives_Native.fst
                                                    y).FStar_Syntax_Syntax.sort in
                                             let uu____12795 =
                                               let uu____12798 =
                                                 names_to_string fvs in
                                               let uu____12799 =
                                                 let uu____12802 =
                                                   names_to_string
                                                     pattern_var_set in
                                                 [uu____12802] in
                                               uu____12798 :: uu____12799 in
                                             uu____12794 :: uu____12795 in
                                           uu____12790 :: uu____12791 in
                                         uu____12774 :: uu____12787 in
                                       FStar_Util.print
                                         "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n"
                                         uu____12771);
                                  aux pat_args pat_args_set pattern_vars
                                    pattern_var_set (formal :: seen_formals)
                                    formals1 res_t tl1)
                               else
                                 (let uu____12804 =
                                    FStar_Util.set_add
                                      (FStar_Pervasives_Native.fst y)
                                      pat_args_set in
                                  let uu____12807 =
                                    FStar_Util.set_add
                                      (FStar_Pervasives_Native.fst formal)
                                      pattern_var_set in
                                  aux (y :: pat_args) uu____12804 (formal ::
                                    pattern_vars) uu____12807 (formal ::
                                    seen_formals) formals1 res_t tl1)))))
                 | ([],uu____12814::uu____12815) ->
                     let uu____12846 =
                       let uu____12859 =
                         FStar_TypeChecker_Normalize.unfold_whnf env res_t in
                       FStar_Syntax_Util.arrow_formals uu____12859 in
                     (match uu____12846 with
                      | (more_formals,res_t1) ->
                          (match more_formals with
                           | [] -> FStar_Pervasives_Native.None
                           | uu____12898 ->
                               aux pat_args pat_args_set pattern_vars
                                 pattern_var_set seen_formals more_formals
                                 res_t1 args1))
                 | (uu____12905::uu____12906,[]) ->
                     FStar_Pervasives_Native.None) in
              let uu____12929 =
                let uu____12942 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k in
                FStar_Syntax_Util.arrow_formals uu____12942 in
              (match uu____12929 with
               | (all_formals,res_t) ->
                   (debug1
                      (fun uu____12978  ->
                         let uu____12979 =
                           FStar_Syntax_Print.term_to_string t in
                         let uu____12980 =
                           FStar_Syntax_Print.binders_to_string ", "
                             all_formals in
                         let uu____12981 =
                           FStar_Syntax_Print.term_to_string res_t in
                         let uu____12982 =
                           FStar_Syntax_Print.args_to_string args in
                         FStar_Util.print4
                           "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n"
                           uu____12979 uu____12980 uu____12981 uu____12982);
                    (let uu____12983 = FStar_Syntax_Syntax.new_bv_set () in
                     let uu____12986 = FStar_Syntax_Syntax.new_bv_set () in
                     aux [] uu____12983 [] uu____12986 [] all_formals res_t
                       args))) in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____13020 = lhs in
          match uu____13020 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____13030 ->
                    let uu____13031 = sn_binders env1 pat_vars1 in
                    u_abs k_uv uu____13031 rhs in
              let wl2 =
                solve_prob orig FStar_Pervasives_Native.None
                  [TERM ((uv, k_uv), sol)] wl1 in
              solve env1 wl2 in
        let imitate orig env1 wl1 p =
          let uu____13054 = p in
          match uu____13054 with
          | (((u,k),xs,c),ps,(h,uu____13065,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13147 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____13147 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13170 = h gs_xs in
                     let uu____13171 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57) in
                     FStar_Syntax_Util.abs xs1 uu____13170 uu____13171 in
                   ((let uu____13177 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____13177
                     then
                       let uu____13178 =
                         let uu____13181 =
                           let uu____13182 =
                             FStar_List.map tc_to_string gs_xs in
                           FStar_All.pipe_right uu____13182
                             (FStar_String.concat "\n\t>") in
                         let uu____13187 =
                           let uu____13190 =
                             FStar_Syntax_Print.binders_to_string ", " xs1 in
                           let uu____13191 =
                             let uu____13194 =
                               FStar_Syntax_Print.comp_to_string c in
                             let uu____13195 =
                               let uu____13198 =
                                 FStar_Syntax_Print.term_to_string im in
                               let uu____13199 =
                                 let uu____13202 =
                                   FStar_Syntax_Print.tag_of_term im in
                                 let uu____13203 =
                                   let uu____13206 =
                                     let uu____13207 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs in
                                     FStar_All.pipe_right uu____13207
                                       (FStar_String.concat ", ") in
                                   let uu____13212 =
                                     let uu____13215 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula in
                                     [uu____13215] in
                                   uu____13206 :: uu____13212 in
                                 uu____13202 :: uu____13203 in
                               uu____13198 :: uu____13199 in
                             uu____13194 :: uu____13195 in
                           uu____13190 :: uu____13191 in
                         uu____13181 :: uu____13187 in
                       FStar_Util.print
                         "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13178
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___248_13236 =
          match uu___248_13236 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____13268 = p in
          match uu____13268 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13359 = FStar_List.nth ps i in
              (match uu____13359 with
               | (pi,uu____13363) ->
                   let uu____13368 = FStar_List.nth xs i in
                   (match uu____13368 with
                    | (xi,uu____13380) ->
                        let rec gs k =
                          let uu____13393 =
                            let uu____13406 =
                              FStar_TypeChecker_Normalize.unfold_whnf env1 k in
                            FStar_Syntax_Util.arrow_formals uu____13406 in
                          match uu____13393 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____13481)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____13494 = new_uvar r xs k_a in
                                    (match uu____13494 with
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
                                         let uu____13516 = aux subst2 tl1 in
                                         (match uu____13516 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____13543 =
                                                let uu____13546 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____13546 :: gi_xs' in
                                              let uu____13547 =
                                                let uu____13550 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____13550 :: gi_ps' in
                                              (uu____13543, uu____13547))) in
                              aux [] bs in
                        let uu____13555 =
                          let uu____13556 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____13556 in
                        if uu____13555
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____13560 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____13560 with
                           | (g_xs,uu____13572) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____13583 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____13584 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_58  ->
                                        FStar_Pervasives_Native.Some _0_58) in
                                 FStar_Syntax_Util.abs xs uu____13583
                                   uu____13584 in
                               let sub1 =
                                 let uu____13590 =
                                   let uu____13595 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____13598 =
                                     let uu____13601 =
                                       FStar_List.map
                                         (fun uu____13616  ->
                                            match uu____13616 with
                                            | (uu____13625,uu____13626,y) ->
                                                y) qs in
                                     FStar_All.pipe_left h uu____13601 in
                                   mk_problem (p_scope orig) orig uu____13595
                                     (p_rel orig) uu____13598
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____13590 in
                               ((let uu____13641 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____13641
                                 then
                                   let uu____13642 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____13643 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____13642 uu____13643
                                 else ());
                                (let wl2 =
                                   let uu____13646 =
                                     let uu____13649 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____13649 in
                                   solve_prob orig uu____13646
                                     [TERM (u, proj)] wl1 in
                                 let uu____13658 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____13658))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____13689 = lhs in
          match uu____13689 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____13725 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____13725 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____13758 =
                        let uu____13805 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____13805) in
                      FStar_Pervasives_Native.Some uu____13758
                    else
                      (let rec elim k args =
                         let k1 =
                           FStar_TypeChecker_Normalize.unfold_whnf env k in
                         let uu____13949 =
                           let uu____13956 =
                             let uu____13957 = FStar_Syntax_Subst.compress k1 in
                             uu____13957.FStar_Syntax_Syntax.n in
                           (uu____13956, args) in
                         match uu____13949 with
                         | (uu____13968,[]) ->
                             let uu____13971 =
                               let uu____13982 =
                                 FStar_Syntax_Syntax.mk_Total k1 in
                               ([], uu____13982) in
                             FStar_Pervasives_Native.Some uu____13971
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____14003,uu____14004) ->
                             let uu____14025 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14025 with
                              | (uv1,uv_args) ->
                                  let uu____14068 =
                                    let uu____14069 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14069.FStar_Syntax_Syntax.n in
                                  (match uu____14068 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14079) ->
                                       let uu____14104 =
                                         pat_vars env [] uv_args in
                                       (match uu____14104 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14131  ->
                                                      let uu____14132 =
                                                        let uu____14133 =
                                                          let uu____14134 =
                                                            let uu____14139 =
                                                              let uu____14140
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14140
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14139 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14134 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14133 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14132)) in
                                            let c1 =
                                              let uu____14150 =
                                                let uu____14151 =
                                                  let uu____14156 =
                                                    let uu____14157 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14157
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14156 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14151 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14150 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14170 =
                                                let uu____14173 =
                                                  let uu____14174 =
                                                    let uu____14177 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14177
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14174 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14173 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14170 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14195 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14200,uu____14201) ->
                             let uu____14220 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14220 with
                              | (uv1,uv_args) ->
                                  let uu____14263 =
                                    let uu____14264 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14264.FStar_Syntax_Syntax.n in
                                  (match uu____14263 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14274) ->
                                       let uu____14299 =
                                         pat_vars env [] uv_args in
                                       (match uu____14299 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14326  ->
                                                      let uu____14327 =
                                                        let uu____14328 =
                                                          let uu____14329 =
                                                            let uu____14334 =
                                                              let uu____14335
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14335
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14334 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14329 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14328 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14327)) in
                                            let c1 =
                                              let uu____14345 =
                                                let uu____14346 =
                                                  let uu____14351 =
                                                    let uu____14352 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14352
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14351 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14346 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14345 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14365 =
                                                let uu____14368 =
                                                  let uu____14369 =
                                                    let uu____14372 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14372
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14369 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14368 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14365 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14390 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____14397) ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____14438 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____14438
                                 (fun _0_61  ->
                                    FStar_Pervasives_Native.Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____14474 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____14474 with
                                  | (args1,rest) ->
                                      let uu____14503 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____14503 with
                                       | (xs2,c2) ->
                                           let uu____14516 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____14516
                                             (fun uu____14540  ->
                                                match uu____14540 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____14580 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____14580 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k1.FStar_Syntax_Syntax.pos in
                                      let uu____14648 =
                                        let uu____14653 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____14653 in
                                      FStar_All.pipe_right uu____14648
                                        (fun _0_62  ->
                                           FStar_Pervasives_Native.Some _0_62))
                         | uu____14668 ->
                             let uu____14675 =
                               let uu____14680 =
                                 let uu____14681 =
                                   FStar_Syntax_Print.uvar_to_string uv in
                                 let uu____14682 =
                                   FStar_Syntax_Print.term_to_string k1 in
                                 let uu____14683 =
                                   FStar_Syntax_Print.term_to_string k_uv in
                                 FStar_Util.format3
                                   "Impossible: ill-typed application %s : %s\n\t%s"
                                   uu____14681 uu____14682 uu____14683 in
                               (FStar_Errors.Fatal_IllTyped, uu____14680) in
                             FStar_Errors.raise_error uu____14675
                               t1.FStar_Syntax_Syntax.pos in
                       let uu____14690 = elim k_uv ps in
                       FStar_Util.bind_opt uu____14690
                         (fun uu____14745  ->
                            match uu____14745 with
                            | (xs1,c1) ->
                                let uu____14794 =
                                  let uu____14835 = decompose env t2 in
                                  (((uv, k_uv), xs1, c1), ps, uu____14835) in
                                FStar_Pervasives_Native.Some uu____14794)) in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail uu____14956 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig in
                let rec try_project st i =
                  if i >= n1
                  then fail ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction () in
                     let uu____14972 = project orig env wl1 i st in
                     match uu____14972 with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some (Failed uu____14986) ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some sol -> sol) in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt in
                  let tx = FStar_Syntax_Unionfind.new_transaction () in
                  let uu____15001 = imitate orig env wl1 st in
                  match uu____15001 with
                  | Failed uu____15006 ->
                      (FStar_Syntax_Unionfind.rollback tx;
                       try_project st (Prims.parse_int "0"))
                  | sol -> sol
                else fail () in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____15037 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1 in
                match uu____15037 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let uu____15060 = forced_lhs_pattern in
                    (match uu____15060 with
                     | (lhs_t,uu____15062,uu____15063,uu____15064) ->
                         ((let uu____15066 =
                             FStar_TypeChecker_Env.debug env
                               (FStar_Options.Other "Rel") in
                           if uu____15066
                           then
                             let uu____15067 = lhs1 in
                             match uu____15067 with
                             | (t0,uu____15069,uu____15070,uu____15071) ->
                                 let uu____15072 = forced_lhs_pattern in
                                 (match uu____15072 with
                                  | (t11,uu____15074,uu____15075,uu____15076)
                                      ->
                                      let uu____15077 =
                                        FStar_Syntax_Print.term_to_string t0 in
                                      let uu____15078 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      FStar_Util.print2
                                        "force_quasi_pattern succeeded, turning %s into %s\n"
                                        uu____15077 uu____15078)
                           else ());
                          (let rhs_vars = FStar_Syntax_Free.names rhs in
                           let lhs_vars = FStar_Syntax_Free.names lhs_t in
                           let uu____15086 =
                             FStar_Util.set_is_subset_of rhs_vars lhs_vars in
                           if uu____15086
                           then
                             ((let uu____15088 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "Rel") in
                               if uu____15088
                               then
                                 let uu____15089 =
                                   FStar_Syntax_Print.term_to_string rhs in
                                 let uu____15090 = names_to_string rhs_vars in
                                 let uu____15091 = names_to_string lhs_vars in
                                 FStar_Util.print3
                                   "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n"
                                   uu____15089 uu____15090 uu____15091
                               else ());
                              (let tx =
                                 FStar_Syntax_Unionfind.new_transaction () in
                               let wl2 =
                                 extend_solution (p_pid orig) [sol] wl1 in
                               let uu____15095 =
                                 let uu____15096 =
                                   FStar_TypeChecker_Common.as_tprob orig in
                                 solve_t env uu____15096 wl2 in
                               match uu____15095 with
                               | Failed uu____15097 ->
                                   (FStar_Syntax_Unionfind.rollback tx;
                                    imitate_or_project n1 lhs1 rhs stopt)
                               | sol1 -> sol1))
                           else
                             ((let uu____15106 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "Rel") in
                               if uu____15106
                               then
                                 FStar_Util.print_string
                                   "fvar check failed for quasi pattern ... im/proj\n"
                               else ());
                              imitate_or_project n1 lhs1 rhs stopt)))) in
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
                     let uu___285_16451 = problem in
                     let uu____16452 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___285_16451.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16452;
                       FStar_TypeChecker_Common.relation =
                         (uu___285_16451.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___285_16451.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___285_16451.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___285_16451.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___285_16451.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___285_16451.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___285_16451.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___285_16451.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16450 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____16453,uu____16454) ->
                   let uu____16461 =
                     let uu___285_16462 = problem in
                     let uu____16463 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___285_16462.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16463;
                       FStar_TypeChecker_Common.relation =
                         (uu___285_16462.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___285_16462.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___285_16462.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___285_16462.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___285_16462.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___285_16462.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___285_16462.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___285_16462.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16461 wl
               | (uu____16464,FStar_Syntax_Syntax.Tm_ascribed uu____16465) ->
                   let uu____16492 =
                     let uu___286_16493 = problem in
                     let uu____16494 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___286_16493.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___286_16493.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___286_16493.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16494;
                       FStar_TypeChecker_Common.element =
                         (uu___286_16493.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___286_16493.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___286_16493.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___286_16493.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___286_16493.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___286_16493.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16492 wl
               | (uu____16495,FStar_Syntax_Syntax.Tm_meta uu____16496) ->
                   let uu____16503 =
                     let uu___286_16504 = problem in
                     let uu____16505 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___286_16504.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___286_16504.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___286_16504.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16505;
                       FStar_TypeChecker_Common.element =
                         (uu___286_16504.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___286_16504.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___286_16504.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___286_16504.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___286_16504.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___286_16504.FStar_TypeChecker_Common.rank)
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
                   let mk_c c uu___249_16564 =
                     match uu___249_16564 with
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
                   let mk_t t l uu___250_16815 =
                     match uu___250_16815 with
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
                            (let uu___287_17094 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___287_17094.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___287_17094.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___287_17094.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___287_17094.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___287_17094.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___287_17094.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___287_17094.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___287_17094.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___287_17094.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___287_17094.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___287_17094.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___287_17094.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___287_17094.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___287_17094.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___287_17094.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___287_17094.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___287_17094.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___287_17094.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___287_17094.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___287_17094.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___287_17094.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___287_17094.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___287_17094.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___287_17094.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___287_17094.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___287_17094.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___287_17094.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___287_17094.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___287_17094.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___287_17094.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___287_17094.FStar_TypeChecker_Env.dep_graph)
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
                          (let uu___288_17167 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___288_17167.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___288_17167.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___288_17167.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___288_17167.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___288_17167.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___288_17167.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___288_17167.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___288_17167.FStar_TypeChecker_Common.rank)
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
                               (let uu___289_17206 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___289_17206.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___289_17206.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___289_17206.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___289_17206.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___289_17206.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___289_17206.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___289_17206.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___289_17206.FStar_TypeChecker_Common.rank)
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
                               (let uu___289_17246 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___289_17246.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___289_17246.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___289_17246.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___289_17246.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___289_17246.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___289_17246.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___289_17246.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___289_17246.FStar_TypeChecker_Common.rank)
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
                            (let uu___287_17365 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___287_17365.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___287_17365.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___287_17365.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___287_17365.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___287_17365.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___287_17365.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___287_17365.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___287_17365.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___287_17365.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___287_17365.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___287_17365.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___287_17365.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___287_17365.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___287_17365.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___287_17365.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___287_17365.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___287_17365.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___287_17365.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___287_17365.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___287_17365.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___287_17365.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___287_17365.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___287_17365.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___287_17365.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___287_17365.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___287_17365.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___287_17365.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___287_17365.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___287_17365.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___287_17365.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___287_17365.FStar_TypeChecker_Env.dep_graph)
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
                          (let uu___288_17438 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___288_17438.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___288_17438.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___288_17438.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___288_17438.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___288_17438.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___288_17438.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___288_17438.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___288_17438.FStar_TypeChecker_Common.rank)
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
                               (let uu___289_17477 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___289_17477.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___289_17477.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___289_17477.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___289_17477.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___289_17477.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___289_17477.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___289_17477.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___289_17477.FStar_TypeChecker_Common.rank)
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
                               (let uu___289_17517 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___289_17517.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___289_17517.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___289_17517.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___289_17517.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___289_17517.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___289_17517.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___289_17517.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___289_17517.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17521 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                   let should_delta =
                     ((let uu____17553 = FStar_Syntax_Free.uvars t1 in
                       FStar_Util.set_is_empty uu____17553) &&
                        (let uu____17565 = FStar_Syntax_Free.uvars t2 in
                         FStar_Util.set_is_empty uu____17565))
                       &&
                       (let uu____17580 =
                          head_matches env x1.FStar_Syntax_Syntax.sort
                            x2.FStar_Syntax_Syntax.sort in
                        match uu____17580 with
                        | MisMatch
                            (FStar_Pervasives_Native.Some
                             d1,FStar_Pervasives_Native.Some d2)
                            ->
                            let is_unfoldable uu___251_17590 =
                              match uu___251_17590 with
                              | FStar_Syntax_Syntax.Delta_constant  -> true
                              | FStar_Syntax_Syntax.Delta_defined_at_level
                                  uu____17591 -> true
                              | uu____17592 -> false in
                            (is_unfoldable d1) && (is_unfoldable d2)
                        | uu____17593 -> false) in
                   let uu____17594 = as_refinement should_delta env wl t1 in
                   (match uu____17594 with
                    | (x11,phi1) ->
                        let uu____17601 =
                          as_refinement should_delta env wl t2 in
                        (match uu____17601 with
                         | (x21,phi21) ->
                             let base_prob =
                               let uu____17609 =
                                 mk_problem (p_scope orig) orig
                                   x11.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x21.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____17609 in
                             let x12 = FStar_Syntax_Syntax.freshen_bv x11 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x12)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi22 =
                               FStar_Syntax_Subst.subst subst1 phi21 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x12 in
                             let mk_imp1 imp phi12 phi23 =
                               let uu____17647 = imp phi12 phi23 in
                               FStar_All.pipe_right uu____17647
                                 (guard_on_element wl problem x12) in
                             let fallback uu____17651 =
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
                                 let uu____17657 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____17657 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____17666 =
                                   let uu____17671 =
                                     let uu____17672 =
                                       let uu____17679 =
                                         FStar_Syntax_Syntax.mk_binder x12 in
                                       [uu____17679] in
                                     FStar_List.append (p_scope orig)
                                       uu____17672 in
                                   mk_problem uu____17671 orig phi11
                                     FStar_TypeChecker_Common.EQ phi22
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____17666 in
                               let uu____17688 =
                                 solve env1
                                   (let uu___290_17690 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___290_17690.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___290_17690.smt_ok);
                                      tcenv = (uu___290_17690.tcenv)
                                    }) in
                               (match uu____17688 with
                                | Failed uu____17697 -> fallback ()
                                | Success uu____17702 ->
                                    let guard =
                                      let uu____17706 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____17711 =
                                        let uu____17712 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____17712
                                          (guard_on_element wl problem x12) in
                                      FStar_Syntax_Util.mk_conj uu____17706
                                        uu____17711 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___291_17721 = wl1 in
                                      {
                                        attempting =
                                          (uu___291_17721.attempting);
                                        wl_deferred =
                                          (uu___291_17721.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___291_17721.defer_ok);
                                        smt_ok = (uu___291_17721.smt_ok);
                                        tcenv = (uu___291_17721.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17723,FStar_Syntax_Syntax.Tm_uvar uu____17724) ->
                   let uu____17757 = destruct_flex_t t1 in
                   let uu____17758 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17757 uu____17758
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17759;
                     FStar_Syntax_Syntax.pos = uu____17760;
                     FStar_Syntax_Syntax.vars = uu____17761;_},uu____17762),FStar_Syntax_Syntax.Tm_uvar
                  uu____17763) ->
                   let uu____17816 = destruct_flex_t t1 in
                   let uu____17817 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17816 uu____17817
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17818,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17819;
                     FStar_Syntax_Syntax.pos = uu____17820;
                     FStar_Syntax_Syntax.vars = uu____17821;_},uu____17822))
                   ->
                   let uu____17875 = destruct_flex_t t1 in
                   let uu____17876 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17875 uu____17876
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17877;
                     FStar_Syntax_Syntax.pos = uu____17878;
                     FStar_Syntax_Syntax.vars = uu____17879;_},uu____17880),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17881;
                     FStar_Syntax_Syntax.pos = uu____17882;
                     FStar_Syntax_Syntax.vars = uu____17883;_},uu____17884))
                   ->
                   let uu____17957 = destruct_flex_t t1 in
                   let uu____17958 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17957 uu____17958
               | (FStar_Syntax_Syntax.Tm_uvar uu____17959,uu____17960) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____17977 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____17977 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17984;
                     FStar_Syntax_Syntax.pos = uu____17985;
                     FStar_Syntax_Syntax.vars = uu____17986;_},uu____17987),uu____17988)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18025 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____18025 t2 wl
               | (uu____18032,FStar_Syntax_Syntax.Tm_uvar uu____18033) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____18050,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18051;
                     FStar_Syntax_Syntax.pos = uu____18052;
                     FStar_Syntax_Syntax.vars = uu____18053;_},uu____18054))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18091,FStar_Syntax_Syntax.Tm_type uu____18092) ->
                   solve_t' env
                     (let uu___292_18110 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___292_18110.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___292_18110.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___292_18110.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___292_18110.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___292_18110.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___292_18110.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___292_18110.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___292_18110.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___292_18110.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18111;
                     FStar_Syntax_Syntax.pos = uu____18112;
                     FStar_Syntax_Syntax.vars = uu____18113;_},uu____18114),FStar_Syntax_Syntax.Tm_type
                  uu____18115) ->
                   solve_t' env
                     (let uu___292_18153 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___292_18153.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___292_18153.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___292_18153.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___292_18153.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___292_18153.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___292_18153.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___292_18153.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___292_18153.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___292_18153.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18154,FStar_Syntax_Syntax.Tm_arrow uu____18155) ->
                   solve_t' env
                     (let uu___292_18185 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___292_18185.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___292_18185.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___292_18185.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___292_18185.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___292_18185.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___292_18185.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___292_18185.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___292_18185.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___292_18185.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18186;
                     FStar_Syntax_Syntax.pos = uu____18187;
                     FStar_Syntax_Syntax.vars = uu____18188;_},uu____18189),FStar_Syntax_Syntax.Tm_arrow
                  uu____18190) ->
                   solve_t' env
                     (let uu___292_18240 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___292_18240.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___292_18240.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___292_18240.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___292_18240.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___292_18240.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___292_18240.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___292_18240.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___292_18240.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___292_18240.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18241,uu____18242) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18261 =
                        let uu____18262 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18262 in
                      if uu____18261
                      then
                        let uu____18263 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___293_18269 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___293_18269.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___293_18269.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___293_18269.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___293_18269.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___293_18269.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___293_18269.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___293_18269.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___293_18269.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___293_18269.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18270 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18263 uu____18270 t2
                          wl
                      else
                        (let uu____18278 = base_and_refinement env t2 in
                         match uu____18278 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18307 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___294_18313 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___294_18313.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___294_18313.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___294_18313.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___294_18313.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___294_18313.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___294_18313.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___294_18313.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___294_18313.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___294_18313.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18314 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18307
                                    uu____18314 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___295_18328 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___295_18328.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___295_18328.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18331 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_72  ->
                                         FStar_TypeChecker_Common.TProb _0_72)
                                      uu____18331 in
                                  let guard =
                                    let uu____18343 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18343
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18351;
                     FStar_Syntax_Syntax.pos = uu____18352;
                     FStar_Syntax_Syntax.vars = uu____18353;_},uu____18354),uu____18355)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18394 =
                        let uu____18395 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18395 in
                      if uu____18394
                      then
                        let uu____18396 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___293_18402 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___293_18402.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___293_18402.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___293_18402.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___293_18402.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___293_18402.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___293_18402.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___293_18402.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___293_18402.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___293_18402.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18403 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18396 uu____18403 t2
                          wl
                      else
                        (let uu____18411 = base_and_refinement env t2 in
                         match uu____18411 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18440 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___294_18446 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___294_18446.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___294_18446.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___294_18446.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___294_18446.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___294_18446.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___294_18446.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___294_18446.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___294_18446.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___294_18446.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18447 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18440
                                    uu____18447 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___295_18461 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___295_18461.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___295_18461.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18464 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_75  ->
                                         FStar_TypeChecker_Common.TProb _0_75)
                                      uu____18464 in
                                  let guard =
                                    let uu____18476 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18476
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18484,FStar_Syntax_Syntax.Tm_uvar uu____18485) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18503 = base_and_refinement env t1 in
                      match uu____18503 with
                      | (t_base,uu____18515) ->
                          solve_t env
                            (let uu___296_18529 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___296_18529.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___296_18529.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___296_18529.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___296_18529.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___296_18529.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___296_18529.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___296_18529.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___296_18529.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18530,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18531;
                     FStar_Syntax_Syntax.pos = uu____18532;
                     FStar_Syntax_Syntax.vars = uu____18533;_},uu____18534))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18572 = base_and_refinement env t1 in
                      match uu____18572 with
                      | (t_base,uu____18584) ->
                          solve_t env
                            (let uu___296_18598 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___296_18598.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___296_18598.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___296_18598.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___296_18598.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___296_18598.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___296_18598.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___296_18598.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___296_18598.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____18599,uu____18600) ->
                   let t21 =
                     let uu____18610 = base_and_refinement env t2 in
                     FStar_All.pipe_left force_refinement uu____18610 in
                   solve_t env
                     (let uu___297_18634 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___297_18634.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___297_18634.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___297_18634.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___297_18634.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___297_18634.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___297_18634.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___297_18634.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___297_18634.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___297_18634.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____18635,FStar_Syntax_Syntax.Tm_refine uu____18636) ->
                   let t11 =
                     let uu____18646 = base_and_refinement env t1 in
                     FStar_All.pipe_left force_refinement uu____18646 in
                   solve_t env
                     (let uu___298_18670 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___298_18670.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___298_18670.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___298_18670.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___298_18670.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___298_18670.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___298_18670.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___298_18670.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___298_18670.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___298_18670.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____18673,uu____18674) ->
                   let head1 =
                     let uu____18700 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18700
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18744 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18744
                       FStar_Pervasives_Native.fst in
                   let uu____18785 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18785
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18800 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18800
                      then
                        let guard =
                          let uu____18812 =
                            let uu____18813 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18813 = FStar_Syntax_Util.Equal in
                          if uu____18812
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18817 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____18817) in
                        let uu____18820 = solve_prob orig guard [] wl in
                        solve env uu____18820
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____18823,uu____18824) ->
                   let head1 =
                     let uu____18834 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18834
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18878 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18878
                       FStar_Pervasives_Native.fst in
                   let uu____18919 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18919
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18934 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18934
                      then
                        let guard =
                          let uu____18946 =
                            let uu____18947 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18947 = FStar_Syntax_Util.Equal in
                          if uu____18946
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18951 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____18951) in
                        let uu____18954 = solve_prob orig guard [] wl in
                        solve env uu____18954
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____18957,uu____18958) ->
                   let head1 =
                     let uu____18962 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18962
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19006 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19006
                       FStar_Pervasives_Native.fst in
                   let uu____19047 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19047
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19062 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19062
                      then
                        let guard =
                          let uu____19074 =
                            let uu____19075 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19075 = FStar_Syntax_Util.Equal in
                          if uu____19074
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19079 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____19079) in
                        let uu____19082 = solve_prob orig guard [] wl in
                        solve env uu____19082
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____19085,uu____19086) ->
                   let head1 =
                     let uu____19090 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19090
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19134 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19134
                       FStar_Pervasives_Native.fst in
                   let uu____19175 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19175
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19190 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19190
                      then
                        let guard =
                          let uu____19202 =
                            let uu____19203 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19203 = FStar_Syntax_Util.Equal in
                          if uu____19202
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19207 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____19207) in
                        let uu____19210 = solve_prob orig guard [] wl in
                        solve env uu____19210
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____19213,uu____19214) ->
                   let head1 =
                     let uu____19218 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19218
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19262 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19262
                       FStar_Pervasives_Native.fst in
                   let uu____19303 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19303
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19318 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19318
                      then
                        let guard =
                          let uu____19330 =
                            let uu____19331 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19331 = FStar_Syntax_Util.Equal in
                          if uu____19330
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19335 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19335) in
                        let uu____19338 = solve_prob orig guard [] wl in
                        solve env uu____19338
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19341,uu____19342) ->
                   let head1 =
                     let uu____19360 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19360
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19404 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19404
                       FStar_Pervasives_Native.fst in
                   let uu____19445 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19445
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19460 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19460
                      then
                        let guard =
                          let uu____19472 =
                            let uu____19473 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19473 = FStar_Syntax_Util.Equal in
                          if uu____19472
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19477 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19477) in
                        let uu____19480 = solve_prob orig guard [] wl in
                        solve env uu____19480
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19483,FStar_Syntax_Syntax.Tm_match uu____19484) ->
                   let head1 =
                     let uu____19510 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19510
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19554 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19554
                       FStar_Pervasives_Native.fst in
                   let uu____19595 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19595
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19610 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19610
                      then
                        let guard =
                          let uu____19622 =
                            let uu____19623 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19623 = FStar_Syntax_Util.Equal in
                          if uu____19622
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19627 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____19627) in
                        let uu____19630 = solve_prob orig guard [] wl in
                        solve env uu____19630
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19633,FStar_Syntax_Syntax.Tm_uinst uu____19634) ->
                   let head1 =
                     let uu____19644 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19644
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19688 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19688
                       FStar_Pervasives_Native.fst in
                   let uu____19729 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19729
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19744 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19744
                      then
                        let guard =
                          let uu____19756 =
                            let uu____19757 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19757 = FStar_Syntax_Util.Equal in
                          if uu____19756
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19761 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____19761) in
                        let uu____19764 = solve_prob orig guard [] wl in
                        solve env uu____19764
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19767,FStar_Syntax_Syntax.Tm_name uu____19768) ->
                   let head1 =
                     let uu____19772 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19772
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19816 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19816
                       FStar_Pervasives_Native.fst in
                   let uu____19857 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19857
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19872 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19872
                      then
                        let guard =
                          let uu____19884 =
                            let uu____19885 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19885 = FStar_Syntax_Util.Equal in
                          if uu____19884
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19889 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____19889) in
                        let uu____19892 = solve_prob orig guard [] wl in
                        solve env uu____19892
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19895,FStar_Syntax_Syntax.Tm_constant uu____19896) ->
                   let head1 =
                     let uu____19900 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19900
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19944 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19944
                       FStar_Pervasives_Native.fst in
                   let uu____19985 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19985
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20000 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20000
                      then
                        let guard =
                          let uu____20012 =
                            let uu____20013 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20013 = FStar_Syntax_Util.Equal in
                          if uu____20012
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20017 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____20017) in
                        let uu____20020 = solve_prob orig guard [] wl in
                        solve env uu____20020
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20023,FStar_Syntax_Syntax.Tm_fvar uu____20024) ->
                   let head1 =
                     let uu____20028 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20028
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20072 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20072
                       FStar_Pervasives_Native.fst in
                   let uu____20113 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20113
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20128 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20128
                      then
                        let guard =
                          let uu____20140 =
                            let uu____20141 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20141 = FStar_Syntax_Util.Equal in
                          if uu____20140
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20145 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____20145) in
                        let uu____20148 = solve_prob orig guard [] wl in
                        solve env uu____20148
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20151,FStar_Syntax_Syntax.Tm_app uu____20152) ->
                   let head1 =
                     let uu____20170 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20170
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20214 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20214
                       FStar_Pervasives_Native.fst in
                   let uu____20255 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20255
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20270 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20270
                      then
                        let guard =
                          let uu____20282 =
                            let uu____20283 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20283 = FStar_Syntax_Util.Equal in
                          if uu____20282
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20287 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____20287) in
                        let uu____20290 = solve_prob orig guard [] wl in
                        solve env uu____20290
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let uu____20293,uu____20294) ->
                   let uu____20307 =
                     let uu____20308 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20309 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20308
                       uu____20309 in
                   failwith uu____20307
               | (FStar_Syntax_Syntax.Tm_delayed uu____20310,uu____20311) ->
                   let uu____20336 =
                     let uu____20337 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20338 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20337
                       uu____20338 in
                   failwith uu____20336
               | (uu____20339,FStar_Syntax_Syntax.Tm_delayed uu____20340) ->
                   let uu____20365 =
                     let uu____20366 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20367 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20366
                       uu____20367 in
                   failwith uu____20365
               | (uu____20368,FStar_Syntax_Syntax.Tm_let uu____20369) ->
                   let uu____20382 =
                     let uu____20383 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20384 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20383
                       uu____20384 in
                   failwith uu____20382
               | uu____20385 -> giveup env "head tag mismatch" orig)))
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
          (let uu____20421 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____20421
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____20423 =
               let uu____20424 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name in
               let uu____20425 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20424 uu____20425 in
             giveup env uu____20423 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____20445  ->
                    fun uu____20446  ->
                      match (uu____20445, uu____20446) with
                      | ((a1,uu____20464),(a2,uu____20466)) ->
                          let uu____20475 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg" in
                          FStar_All.pipe_left
                            (fun _0_88  ->
                               FStar_TypeChecker_Common.TProb _0_88)
                            uu____20475)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args in
             let guard =
               let uu____20485 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs in
               FStar_Syntax_Util.mk_conj_l uu____20485 in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
             solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____20509 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20516)::[] -> wp1
              | uu____20533 ->
                  let uu____20542 =
                    let uu____20543 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20543 in
                  failwith uu____20542 in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____20551 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ in
                  [uu____20551]
              | x -> x in
            let uu____20553 =
              let uu____20562 =
                let uu____20563 =
                  let uu____20564 = FStar_List.hd univs1 in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____20564 c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____20563 in
              [uu____20562] in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20553;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20565 = lift_c1 () in solve_eq uu____20565 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___252_20571  ->
                       match uu___252_20571 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20572 -> false)) in
             let uu____20573 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20607)::uu____20608,(wp2,uu____20610)::uu____20611)
                   -> (wp1, wp2)
               | uu____20668 ->
                   let uu____20689 =
                     let uu____20694 =
                       let uu____20695 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name in
                       let uu____20696 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____20695 uu____20696 in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____20694) in
                   FStar_Errors.raise_error uu____20689
                     env.FStar_TypeChecker_Env.range in
             match uu____20573 with
             | (wpc1,wpc2) ->
                 let uu____20715 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____20715
                 then
                   let uu____20718 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____20718 wl
                 else
                   (let uu____20722 =
                      let uu____20729 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____20729 in
                    match uu____20722 with
                    | (c2_decl,qualifiers) ->
                        let uu____20750 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____20750
                        then
                          let c1_repr =
                            let uu____20754 =
                              let uu____20755 =
                                let uu____20756 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____20756 in
                              let uu____20757 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20755 uu____20757 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20754 in
                          let c2_repr =
                            let uu____20759 =
                              let uu____20760 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____20761 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20760 uu____20761 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20759 in
                          let prob =
                            let uu____20763 =
                              let uu____20768 =
                                let uu____20769 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____20770 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____20769
                                  uu____20770 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____20768 in
                            FStar_TypeChecker_Common.TProb uu____20763 in
                          let wl1 =
                            let uu____20772 =
                              let uu____20775 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____20775 in
                            solve_prob orig uu____20772 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____20784 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____20784
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ in
                                   let uu____20787 =
                                     let uu____20790 =
                                       let uu____20791 =
                                         let uu____20806 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____20807 =
                                           let uu____20810 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____20811 =
                                             let uu____20814 =
                                               let uu____20815 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20815 in
                                             [uu____20814] in
                                           uu____20810 :: uu____20811 in
                                         (uu____20806, uu____20807) in
                                       FStar_Syntax_Syntax.Tm_app uu____20791 in
                                     FStar_Syntax_Syntax.mk uu____20790 in
                                   uu____20787 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ in
                                  let uu____20824 =
                                    let uu____20827 =
                                      let uu____20828 =
                                        let uu____20843 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____20844 =
                                          let uu____20847 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____20848 =
                                            let uu____20851 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____20852 =
                                              let uu____20855 =
                                                let uu____20856 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20856 in
                                              [uu____20855] in
                                            uu____20851 :: uu____20852 in
                                          uu____20847 :: uu____20848 in
                                        (uu____20843, uu____20844) in
                                      FStar_Syntax_Syntax.Tm_app uu____20828 in
                                    FStar_Syntax_Syntax.mk uu____20827 in
                                  uu____20824 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____20863 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____20863 in
                           let wl1 =
                             let uu____20873 =
                               let uu____20876 =
                                 let uu____20879 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____20879 g in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____20876 in
                             solve_prob orig uu____20873 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____20892 = FStar_Util.physical_equality c1 c2 in
        if uu____20892
        then
          let uu____20893 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____20893
        else
          ((let uu____20896 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____20896
            then
              let uu____20897 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____20898 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____20897
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____20898
            else ());
           (let uu____20900 =
              let uu____20905 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____20906 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____20905, uu____20906) in
            match uu____20900 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20910),FStar_Syntax_Syntax.Total
                    (t2,uu____20912)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____20929 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20929 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20932,FStar_Syntax_Syntax.Total uu____20933) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20951),FStar_Syntax_Syntax.Total
                    (t2,uu____20953)) ->
                     let uu____20970 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20970 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20974),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20976)) ->
                     let uu____20993 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20993 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20997),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20999)) ->
                     let uu____21016 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____21016 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21019,FStar_Syntax_Syntax.Comp uu____21020) ->
                     let uu____21029 =
                       let uu___299_21034 = problem in
                       let uu____21039 =
                         let uu____21040 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21040 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___299_21034.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21039;
                         FStar_TypeChecker_Common.relation =
                           (uu___299_21034.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___299_21034.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___299_21034.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___299_21034.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___299_21034.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___299_21034.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___299_21034.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___299_21034.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21029 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21041,FStar_Syntax_Syntax.Comp uu____21042) ->
                     let uu____21051 =
                       let uu___299_21056 = problem in
                       let uu____21061 =
                         let uu____21062 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21062 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___299_21056.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21061;
                         FStar_TypeChecker_Common.relation =
                           (uu___299_21056.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___299_21056.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___299_21056.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___299_21056.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___299_21056.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___299_21056.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___299_21056.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___299_21056.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21051 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21063,FStar_Syntax_Syntax.GTotal uu____21064) ->
                     let uu____21073 =
                       let uu___300_21078 = problem in
                       let uu____21083 =
                         let uu____21084 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21084 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___300_21078.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___300_21078.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___300_21078.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21083;
                         FStar_TypeChecker_Common.element =
                           (uu___300_21078.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___300_21078.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___300_21078.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___300_21078.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___300_21078.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___300_21078.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21073 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21085,FStar_Syntax_Syntax.Total uu____21086) ->
                     let uu____21095 =
                       let uu___300_21100 = problem in
                       let uu____21105 =
                         let uu____21106 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21106 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___300_21100.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___300_21100.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___300_21100.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21105;
                         FStar_TypeChecker_Common.element =
                           (uu___300_21100.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___300_21100.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___300_21100.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___300_21100.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___300_21100.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___300_21100.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21095 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21107,FStar_Syntax_Syntax.Comp uu____21108) ->
                     let uu____21109 =
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
                     if uu____21109
                     then
                       let uu____21110 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____21110 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21116 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21126 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____21127 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____21126, uu____21127)) in
                          match uu____21116 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu____21134 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____21134
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21136 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____21136 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21139 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____21141 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____21141) in
                                if uu____21139
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
                                  (let uu____21144 =
                                     let uu____21145 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____21146 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____21145 uu____21146 in
                                   giveup env uu____21144 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____21151 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21189  ->
              match uu____21189 with
              | (uu____21202,uu____21203,u,uu____21205,uu____21206,uu____21207)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____21151 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____21238 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____21238 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____21256 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21284  ->
                match uu____21284 with
                | (u1,u2) ->
                    let uu____21291 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____21292 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____21291 uu____21292)) in
      FStar_All.pipe_right uu____21256 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21309,[])) -> "{}"
      | uu____21334 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21351 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____21351
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____21354 =
              FStar_List.map
                (fun uu____21364  ->
                   match uu____21364 with
                   | (uu____21369,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____21354 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____21374 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21374 imps
let new_t_problem:
  'Auu____21382 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21382 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21382)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21416 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel") in
                if uu____21416
                then
                  let uu____21417 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs in
                  let uu____21418 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21417
                    (rel_to_string rel) uu____21418
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
            let uu____21442 =
              let uu____21445 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____21445 in
            FStar_Syntax_Syntax.new_bv uu____21442 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____21454 =
              let uu____21457 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____21457 in
            let uu____21460 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____21454 uu____21460 in
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
          let uu____21490 = FStar_Options.eager_inference () in
          if uu____21490
          then
            let uu___301_21491 = probs in
            {
              attempting = (uu___301_21491.attempting);
              wl_deferred = (uu___301_21491.wl_deferred);
              ctr = (uu___301_21491.ctr);
              defer_ok = false;
              smt_ok = (uu___301_21491.smt_ok);
              tcenv = (uu___301_21491.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            ((let uu____21502 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____21502
              then
                let uu____21503 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____21503
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
          ((let uu____21517 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____21517
            then
              let uu____21518 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21518
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f in
            (let uu____21522 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____21522
             then
               let uu____21523 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21523
             else ());
            (let f2 =
               let uu____21526 =
                 let uu____21527 = FStar_Syntax_Util.unmeta f1 in
                 uu____21527.FStar_Syntax_Syntax.n in
               match uu____21526 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21531 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___302_21532 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___302_21532.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___302_21532.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___302_21532.FStar_TypeChecker_Env.implicits)
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
            let uu____21551 =
              let uu____21552 =
                let uu____21553 =
                  let uu____21554 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____21554
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21553;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____21552 in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____21551
let with_guard_no_simp:
  'Auu____21581 .
    'Auu____21581 ->
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
            let uu____21601 =
              let uu____21602 =
                let uu____21603 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____21603
                  (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
              {
                FStar_TypeChecker_Env.guard_f = uu____21602;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              } in
            FStar_Pervasives_Native.Some uu____21601
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
          (let uu____21641 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21641
           then
             let uu____21642 = FStar_Syntax_Print.term_to_string t1 in
             let uu____21643 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21642
               uu____21643
           else ());
          (let prob =
             let uu____21646 =
               let uu____21651 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____21651 in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____21646 in
           let g =
             let uu____21659 =
               let uu____21662 = singleton' env prob smt_ok in
               solve_and_commit env uu____21662
                 (fun uu____21664  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____21659 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21682 = try_teq true env t1 t2 in
        match uu____21682 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____21686 = FStar_TypeChecker_Env.get_range env in
              let uu____21687 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1 in
              FStar_Errors.log_issue uu____21686 uu____21687);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21694 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____21694
              then
                let uu____21695 = FStar_Syntax_Print.term_to_string t1 in
                let uu____21696 = FStar_Syntax_Print.term_to_string t2 in
                let uu____21697 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21695
                  uu____21696 uu____21697
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
          let uu____21711 = FStar_TypeChecker_Env.get_range env in
          let uu____21712 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.log_issue uu____21711 uu____21712
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____21729 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____21729
         then
           let uu____21730 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____21731 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____21730
             uu____21731
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____21736 =
             let uu____21741 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____21741 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____21736 in
         let uu____21746 =
           let uu____21749 = singleton env prob in
           solve_and_commit env uu____21749
             (fun uu____21751  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____21746)
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
      fun uu____21780  ->
        match uu____21780 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____21819 =
                 let uu____21824 =
                   let uu____21825 = FStar_Syntax_Print.univ_to_string u1 in
                   let uu____21826 = FStar_Syntax_Print.univ_to_string u2 in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____21825 uu____21826 in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____21824) in
               let uu____21827 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu____21819 uu____21827) in
            let equiv1 v1 v' =
              let uu____21835 =
                let uu____21840 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____21841 = FStar_Syntax_Subst.compress_univ v' in
                (uu____21840, uu____21841) in
              match uu____21835 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____21860 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____21890 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____21890 with
                      | FStar_Syntax_Syntax.U_unif uu____21897 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____21926  ->
                                    match uu____21926 with
                                    | (u,v') ->
                                        let uu____21935 = equiv1 v1 v' in
                                        if uu____21935
                                        then
                                          let uu____21938 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____21938 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____21954 -> [])) in
            let uu____21959 =
              let wl =
                let uu___303_21963 = empty_worklist env in
                {
                  attempting = (uu___303_21963.attempting);
                  wl_deferred = (uu___303_21963.wl_deferred);
                  ctr = (uu___303_21963.ctr);
                  defer_ok = false;
                  smt_ok = (uu___303_21963.smt_ok);
                  tcenv = (uu___303_21963.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____21981  ->
                      match uu____21981 with
                      | (lb,v1) ->
                          let uu____21988 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____21988 with
                           | USolved wl1 -> ()
                           | uu____21990 -> fail lb v1))) in
            let rec check_ineq uu____21998 =
              match uu____21998 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22007) -> true
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
                      uu____22030,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22032,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22043) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22050,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22058 -> false) in
            let uu____22063 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22078  ->
                      match uu____22078 with
                      | (u,v1) ->
                          let uu____22085 = check_ineq (u, v1) in
                          if uu____22085
                          then true
                          else
                            ((let uu____22088 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____22088
                              then
                                let uu____22089 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____22090 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____22089
                                  uu____22090
                              else ());
                             false))) in
            if uu____22063
            then ()
            else
              ((let uu____22094 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____22094
                then
                  ((let uu____22096 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22096);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22106 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22106))
                else ());
               (let uu____22116 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____22116))
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
      let fail uu____22164 =
        match uu____22164 with
        | (d,s) ->
            let msg = explain env d s in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
              (p_loc d) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____22178 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____22178
       then
         let uu____22179 = wl_to_string wl in
         let uu____22180 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22179 uu____22180
       else ());
      (let g1 =
         let uu____22195 = solve_and_commit env wl fail in
         match uu____22195 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___304_22208 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___304_22208.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___304_22208.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___304_22208.FStar_TypeChecker_Env.implicits)
             }
         | uu____22213 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___305_22217 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___305_22217.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___305_22217.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___305_22217.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____22239 = FStar_ST.op_Bang last_proof_ns in
    match uu____22239 with
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
            let uu___306_22429 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___306_22429.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___306_22429.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___306_22429.FStar_TypeChecker_Env.implicits)
            } in
          let uu____22430 =
            let uu____22431 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____22431 in
          if uu____22430
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22439 = FStar_TypeChecker_Env.get_range env in
                     let uu____22440 =
                       let uu____22441 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22441 in
                     FStar_Errors.diag uu____22439 uu____22440)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   if debug1
                   then
                     (let uu____22445 = FStar_TypeChecker_Env.get_range env in
                      let uu____22446 =
                        let uu____22447 =
                          FStar_Syntax_Print.term_to_string vc1 in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22447 in
                      FStar_Errors.diag uu____22445 uu____22446)
                   else ();
                   (let uu____22449 = check_trivial vc1 in
                    match uu____22449 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22456 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22457 =
                                let uu____22458 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22458 in
                              FStar_Errors.diag uu____22456 uu____22457)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22463 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22464 =
                                let uu____22465 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22465 in
                              FStar_Errors.diag uu____22463 uu____22464)
                           else ();
                           (let vcs =
                              let uu____22476 = FStar_Options.use_tactics () in
                              if uu____22476
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22495  ->
                                     (let uu____22497 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics" in
                                      FStar_All.pipe_left
                                        FStar_Pervasives.ignore uu____22497);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____22499 =
                                   let uu____22506 = FStar_Options.peek () in
                                   (env, vc2, uu____22506) in
                                 [uu____22499]) in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22540  ->
                                    match uu____22540 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal in
                                        let uu____22551 = check_trivial goal1 in
                                        (match uu____22551 with
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
                                                (let uu____22559 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22560 =
                                                   let uu____22561 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   let uu____22562 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1 in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22561 uu____22562 in
                                                 FStar_Errors.diag
                                                   uu____22559 uu____22560)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22565 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22566 =
                                                   let uu____22567 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22567 in
                                                 FStar_Errors.diag
                                                   uu____22565 uu____22566)
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
      let uu____22577 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____22577 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22583 = FStar_TypeChecker_Env.get_range env in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____22583
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____22590 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____22590 with
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
          let uu____22609 = FStar_Syntax_Unionfind.find u in
          match uu____22609 with
          | FStar_Pervasives_Native.None  -> true
          | uu____22612 -> false in
        let rec until_fixpoint acc implicits =
          let uu____22630 = acc in
          match uu____22630 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____22716 = hd1 in
                   (match uu____22716 with
                    | (uu____22729,env,u,tm,k,r) ->
                        let uu____22735 = unresolved u in
                        if uu____22735
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let env1 =
                             FStar_TypeChecker_Env.set_expected_typ env k in
                           let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env1 tm in
                           (let uu____22766 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck") in
                            if uu____22766
                            then
                              let uu____22767 =
                                FStar_Syntax_Print.uvar_to_string u in
                              let uu____22768 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____22769 =
                                FStar_Syntax_Print.term_to_string k in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____22767 uu____22768 uu____22769
                            else ());
                           (let env2 =
                              if forcelax
                              then
                                let uu___307_22772 = env1 in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___307_22772.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___307_22772.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___307_22772.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___307_22772.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___307_22772.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___307_22772.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___307_22772.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___307_22772.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___307_22772.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___307_22772.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___307_22772.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___307_22772.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___307_22772.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___307_22772.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___307_22772.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___307_22772.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___307_22772.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___307_22772.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax = true;
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___307_22772.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___307_22772.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___307_22772.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___307_22772.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___307_22772.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___307_22772.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___307_22772.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___307_22772.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___307_22772.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___307_22772.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___307_22772.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___307_22772.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___307_22772.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___307_22772.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.dep_graph =
                                    (uu___307_22772.FStar_TypeChecker_Env.dep_graph)
                                }
                              else env1 in
                            let g1 =
                              try
                                if must_total
                                then
                                  let uu____22781 =
                                    env2.FStar_TypeChecker_Env.type_of
                                      (let uu___310_22789 = env2 in
                                       {
                                         FStar_TypeChecker_Env.solver =
                                           (uu___310_22789.FStar_TypeChecker_Env.solver);
                                         FStar_TypeChecker_Env.range =
                                           (uu___310_22789.FStar_TypeChecker_Env.range);
                                         FStar_TypeChecker_Env.curmodule =
                                           (uu___310_22789.FStar_TypeChecker_Env.curmodule);
                                         FStar_TypeChecker_Env.gamma =
                                           (uu___310_22789.FStar_TypeChecker_Env.gamma);
                                         FStar_TypeChecker_Env.gamma_cache =
                                           (uu___310_22789.FStar_TypeChecker_Env.gamma_cache);
                                         FStar_TypeChecker_Env.modules =
                                           (uu___310_22789.FStar_TypeChecker_Env.modules);
                                         FStar_TypeChecker_Env.expected_typ =
                                           (uu___310_22789.FStar_TypeChecker_Env.expected_typ);
                                         FStar_TypeChecker_Env.sigtab =
                                           (uu___310_22789.FStar_TypeChecker_Env.sigtab);
                                         FStar_TypeChecker_Env.is_pattern =
                                           (uu___310_22789.FStar_TypeChecker_Env.is_pattern);
                                         FStar_TypeChecker_Env.instantiate_imp
                                           =
                                           (uu___310_22789.FStar_TypeChecker_Env.instantiate_imp);
                                         FStar_TypeChecker_Env.effects =
                                           (uu___310_22789.FStar_TypeChecker_Env.effects);
                                         FStar_TypeChecker_Env.generalize =
                                           (uu___310_22789.FStar_TypeChecker_Env.generalize);
                                         FStar_TypeChecker_Env.letrecs =
                                           (uu___310_22789.FStar_TypeChecker_Env.letrecs);
                                         FStar_TypeChecker_Env.top_level =
                                           (uu___310_22789.FStar_TypeChecker_Env.top_level);
                                         FStar_TypeChecker_Env.check_uvars =
                                           (uu___310_22789.FStar_TypeChecker_Env.check_uvars);
                                         FStar_TypeChecker_Env.use_eq =
                                           (uu___310_22789.FStar_TypeChecker_Env.use_eq);
                                         FStar_TypeChecker_Env.is_iface =
                                           (uu___310_22789.FStar_TypeChecker_Env.is_iface);
                                         FStar_TypeChecker_Env.admit =
                                           (uu___310_22789.FStar_TypeChecker_Env.admit);
                                         FStar_TypeChecker_Env.lax =
                                           (uu___310_22789.FStar_TypeChecker_Env.lax);
                                         FStar_TypeChecker_Env.lax_universes
                                           =
                                           (uu___310_22789.FStar_TypeChecker_Env.lax_universes);
                                         FStar_TypeChecker_Env.failhard =
                                           (uu___310_22789.FStar_TypeChecker_Env.failhard);
                                         FStar_TypeChecker_Env.nosynth =
                                           (uu___310_22789.FStar_TypeChecker_Env.nosynth);
                                         FStar_TypeChecker_Env.tc_term =
                                           (uu___310_22789.FStar_TypeChecker_Env.tc_term);
                                         FStar_TypeChecker_Env.type_of =
                                           (uu___310_22789.FStar_TypeChecker_Env.type_of);
                                         FStar_TypeChecker_Env.universe_of =
                                           (uu___310_22789.FStar_TypeChecker_Env.universe_of);
                                         FStar_TypeChecker_Env.use_bv_sorts =
                                           true;
                                         FStar_TypeChecker_Env.qname_and_index
                                           =
                                           (uu___310_22789.FStar_TypeChecker_Env.qname_and_index);
                                         FStar_TypeChecker_Env.proof_ns =
                                           (uu___310_22789.FStar_TypeChecker_Env.proof_ns);
                                         FStar_TypeChecker_Env.synth =
                                           (uu___310_22789.FStar_TypeChecker_Env.synth);
                                         FStar_TypeChecker_Env.is_native_tactic
                                           =
                                           (uu___310_22789.FStar_TypeChecker_Env.is_native_tactic);
                                         FStar_TypeChecker_Env.identifier_info
                                           =
                                           (uu___310_22789.FStar_TypeChecker_Env.identifier_info);
                                         FStar_TypeChecker_Env.tc_hooks =
                                           (uu___310_22789.FStar_TypeChecker_Env.tc_hooks);
                                         FStar_TypeChecker_Env.dsenv =
                                           (uu___310_22789.FStar_TypeChecker_Env.dsenv);
                                         FStar_TypeChecker_Env.dep_graph =
                                           (uu___310_22789.FStar_TypeChecker_Env.dep_graph)
                                       }) tm1 in
                                  match uu____22781 with
                                  | (uu____22790,uu____22791,g1) -> g1
                                else
                                  (let uu____22794 =
                                     env2.FStar_TypeChecker_Env.tc_term
                                       (let uu___311_22802 = env2 in
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (uu___311_22802.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (uu___311_22802.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (uu___311_22802.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (uu___311_22802.FStar_TypeChecker_Env.gamma);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (uu___311_22802.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (uu___311_22802.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (uu___311_22802.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (uu___311_22802.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.is_pattern =
                                            (uu___311_22802.FStar_TypeChecker_Env.is_pattern);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (uu___311_22802.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (uu___311_22802.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (uu___311_22802.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (uu___311_22802.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (uu___311_22802.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (uu___311_22802.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq =
                                            (uu___311_22802.FStar_TypeChecker_Env.use_eq);
                                          FStar_TypeChecker_Env.is_iface =
                                            (uu___311_22802.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (uu___311_22802.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax =
                                            (uu___311_22802.FStar_TypeChecker_Env.lax);
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (uu___311_22802.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.failhard =
                                            (uu___311_22802.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (uu___311_22802.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.tc_term =
                                            (uu___311_22802.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.type_of =
                                            (uu___311_22802.FStar_TypeChecker_Env.type_of);
                                          FStar_TypeChecker_Env.universe_of =
                                            (uu___311_22802.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            = true;
                                          FStar_TypeChecker_Env.qname_and_index
                                            =
                                            (uu___311_22802.FStar_TypeChecker_Env.qname_and_index);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (uu___311_22802.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth =
                                            (uu___311_22802.FStar_TypeChecker_Env.synth);
                                          FStar_TypeChecker_Env.is_native_tactic
                                            =
                                            (uu___311_22802.FStar_TypeChecker_Env.is_native_tactic);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (uu___311_22802.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (uu___311_22802.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (uu___311_22802.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.dep_graph =
                                            (uu___311_22802.FStar_TypeChecker_Env.dep_graph)
                                        }) tm1 in
                                   match uu____22794 with
                                   | (uu____22803,uu____22804,g1) -> g1)
                              with
                              | e ->
                                  ((let uu____22812 =
                                      let uu____22821 =
                                        let uu____22828 =
                                          let uu____22829 =
                                            FStar_Syntax_Print.uvar_to_string
                                              u in
                                          let uu____22830 =
                                            FStar_TypeChecker_Normalize.term_to_string
                                              env2 tm1 in
                                          FStar_Util.format2
                                            "Failed while checking implicit %s set to %s"
                                            uu____22829 uu____22830 in
                                        (FStar_Errors.Error_BadImplicit,
                                          uu____22828, r) in
                                      [uu____22821] in
                                    FStar_Errors.add_errors uu____22812);
                                   FStar_Exn.raise e) in
                            let g2 =
                              if env2.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___312_22844 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___312_22844.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___312_22844.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___312_22844.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____22847 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____22853  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env2 g2 true in
                              match uu____22847 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
        let uu___313_22881 = g in
        let uu____22882 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___313_22881.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___313_22881.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___313_22881.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____22882
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
        let uu____22936 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____22936 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____22949 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____22949
      | (reason,uu____22951,uu____22952,e,t,r)::uu____22956 ->
          let uu____22983 =
            let uu____22988 =
              let uu____22989 = FStar_Syntax_Print.term_to_string t in
              let uu____22990 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format2
                "Failed to resolve implicit argument of type '%s' introduced in %s"
                uu____22989 uu____22990 in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____22988) in
          FStar_Errors.raise_error uu____22983 r
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___314_22997 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___314_22997.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___314_22997.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___314_22997.FStar_TypeChecker_Env.implicits)
      }
let discharge_guard_nosmt:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool =
  fun env  ->
    fun g  ->
      let uu____23020 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____23020 with
      | FStar_Pervasives_Native.Some uu____23025 -> true
      | FStar_Pervasives_Native.None  -> false
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23035 = try_teq false env t1 t2 in
        match uu____23035 with
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
        (let uu____23055 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____23055
         then
           let uu____23056 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____23057 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23056
             uu____23057
         else ());
        (let uu____23059 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
         match uu____23059 with
         | (prob,x) ->
             let g =
               let uu____23075 =
                 let uu____23078 = singleton' env prob true in
                 solve_and_commit env uu____23078
                   (fun uu____23080  -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____23075 in
             ((let uu____23090 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g) in
               if uu____23090
               then
                 let uu____23091 =
                   FStar_TypeChecker_Normalize.term_to_string env t1 in
                 let uu____23092 =
                   FStar_TypeChecker_Normalize.term_to_string env t2 in
                 let uu____23093 =
                   let uu____23094 = FStar_Util.must g in
                   guard_to_string env uu____23094 in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23091 uu____23092 uu____23093
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
        let uu____23122 = check_subtyping env t1 t2 in
        match uu____23122 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23141 =
              let uu____23142 = FStar_Syntax_Syntax.mk_binder x in
              abstract_guard uu____23142 g in
            FStar_Pervasives_Native.Some uu____23141
let get_subtyping_prop:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23154 = check_subtyping env t1 t2 in
        match uu____23154 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23173 =
              let uu____23174 =
                let uu____23175 = FStar_Syntax_Syntax.mk_binder x in
                [uu____23175] in
              close_guard env uu____23174 g in
            FStar_Pervasives_Native.Some uu____23173
let subtype_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23186 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____23186
         then
           let uu____23187 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____23188 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23187
             uu____23188
         else ());
        (let uu____23190 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
         match uu____23190 with
         | (prob,x) ->
             let g =
               let uu____23200 =
                 let uu____23203 = singleton' env prob false in
                 solve_and_commit env uu____23203
                   (fun uu____23205  -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____23200 in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23216 =
                      let uu____23217 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____23217] in
                    close_guard env uu____23216 g1 in
                  discharge_guard_nosmt env g2))