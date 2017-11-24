
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
{attempting : FStar_TypeChecker_Common.probs; wl_deferred : (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list; ctr : Prims.int; defer_ok : Prims.bool; smt_ok : Prims.bool; tcenv : FStar_TypeChecker_Env.env}


let __proj__Mkworklist__item__attempting : worklist  ->  FStar_TypeChecker_Common.probs = (fun projectee -> (match (projectee) with
| {attempting = __fname__attempting; wl_deferred = __fname__wl_deferred; ctr = __fname__ctr; defer_ok = __fname__defer_ok; smt_ok = __fname__smt_ok; tcenv = __fname__tcenv} -> begin
__fname__attempting
end))


let __proj__Mkworklist__item__wl_deferred : worklist  ->  (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list = (fun projectee -> (match (projectee) with
| {attempting = __fname__attempting; wl_deferred = __fname__wl_deferred; ctr = __fname__ctr; defer_ok = __fname__defer_ok; smt_ok = __fname__smt_ok; tcenv = __fname__tcenv} -> begin
__fname__wl_deferred
end))


let __proj__Mkworklist__item__ctr : worklist  ->  Prims.int = (fun projectee -> (match (projectee) with
| {attempting = __fname__attempting; wl_deferred = __fname__wl_deferred; ctr = __fname__ctr; defer_ok = __fname__defer_ok; smt_ok = __fname__smt_ok; tcenv = __fname__tcenv} -> begin
__fname__ctr
end))


let __proj__Mkworklist__item__defer_ok : worklist  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {attempting = __fname__attempting; wl_deferred = __fname__wl_deferred; ctr = __fname__ctr; defer_ok = __fname__defer_ok; smt_ok = __fname__smt_ok; tcenv = __fname__tcenv} -> begin
__fname__defer_ok
end))


let __proj__Mkworklist__item__smt_ok : worklist  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {attempting = __fname__attempting; wl_deferred = __fname__wl_deferred; ctr = __fname__ctr; defer_ok = __fname__defer_ok; smt_ok = __fname__smt_ok; tcenv = __fname__tcenv} -> begin
__fname__smt_ok
end))


let __proj__Mkworklist__item__tcenv : worklist  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {attempting = __fname__attempting; wl_deferred = __fname__wl_deferred; ctr = __fname__ctr; defer_ok = __fname__defer_ok; smt_ok = __fname__smt_ok; tcenv = __fname__tcenv} -> begin
__fname__tcenv
end))

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
(FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem


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
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____936 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\n\t%s \n\t\t%s\n\t%s" uu____935
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____936
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___218_942  ->
      match uu___218_942 with
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
        let uu___249_1062 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___249_1062.wl_deferred);
          ctr = (uu___249_1062.ctr);
          defer_ok = (uu___249_1062.defer_ok);
          smt_ok;
          tcenv = (uu___249_1062.tcenv)
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
      let uu___250_1093 = empty_worklist env in
      let uu____1094 = FStar_List.map FStar_Pervasives_Native.snd g in
      {
        attempting = uu____1094;
        wl_deferred = (uu___250_1093.wl_deferred);
        ctr = (uu___250_1093.ctr);
        defer_ok = false;
        smt_ok = (uu___250_1093.smt_ok);
        tcenv = (uu___250_1093.tcenv)
      }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___251_1108 = wl in
        {
          attempting = (uu___251_1108.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___251_1108.ctr);
          defer_ok = (uu___251_1108.defer_ok);
          smt_ok = (uu___251_1108.smt_ok);
          tcenv = (uu___251_1108.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___252_1125 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___252_1125.wl_deferred);
        ctr = (uu___252_1125.ctr);
        defer_ok = (uu___252_1125.defer_ok);
        smt_ok = (uu___252_1125.smt_ok);
        tcenv = (uu___252_1125.tcenv)
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
  fun uu___219_1141  ->
    match uu___219_1141 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert:
  'Auu____1145 'Auu____1146 .
    ('Auu____1146,'Auu____1145) FStar_TypeChecker_Common.problem ->
      ('Auu____1146,'Auu____1145) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___253_1163 = p in
    {
      FStar_TypeChecker_Common.pid =
        (uu___253_1163.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___253_1163.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___253_1163.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___253_1163.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___253_1163.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___253_1163.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___253_1163.FStar_TypeChecker_Common.rank)
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
  fun uu___220_1192  ->
    match uu___220_1192 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.CProb _0_42)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___221_1216  ->
      match uu___221_1216 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___222_1219  ->
    match uu___222_1219 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___223_1232  ->
    match uu___223_1232 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___224_1247  ->
    match uu___224_1247 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___225_1262  ->
    match uu___225_1262 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___226_1279  ->
    match uu___226_1279 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___227_1296  ->
    match uu___227_1296 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___228_1309  ->
    match uu___228_1309 with
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
         (fun uu___229_1679  ->
            match uu___229_1679 with
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
        (fun uu___230_1713  ->
           match uu___230_1713 with
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
        (fun uu___231_1748  ->
           match uu___231_1748 with
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
                    let uu___254_1840 = x in
                    let uu____1841 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___254_1840.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___254_1840.FStar_Syntax_Syntax.index);
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
                 (let uu___255_3129 = wl in
                  {
                    attempting = (uu___255_3129.attempting);
                    wl_deferred = (uu___255_3129.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___255_3129.defer_ok);
                    smt_ok = (uu___255_3129.smt_ok);
                    tcenv = (uu___255_3129.tcenv)
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
        (let uu___256_3154 = wl in
         {
           attempting = (uu___256_3154.attempting);
           wl_deferred = (uu___256_3154.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___256_3154.defer_ok);
           smt_ok = (uu___256_3154.smt_ok);
           tcenv = (uu___256_3154.tcenv)
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
  fun uu___232_4740  ->
    match uu___232_4740 with
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
            let uu____5059 = FStar_Const.eq_const c d in
            if uu____5059
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5066),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5068)) ->
            let uu____5117 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____5117
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5124),FStar_Syntax_Syntax.Tm_refine (y,uu____5126)) ->
            let uu____5135 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5135 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5137),uu____5138) ->
            let uu____5143 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____5143 head_match
        | (uu____5144,FStar_Syntax_Syntax.Tm_refine (x,uu____5146)) ->
            let uu____5151 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5151 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5152,FStar_Syntax_Syntax.Tm_type
           uu____5153) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5154,FStar_Syntax_Syntax.Tm_arrow uu____5155) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5181),FStar_Syntax_Syntax.Tm_app (head',uu____5183))
            ->
            let uu____5224 = head_matches env head1 head' in
            FStar_All.pipe_right uu____5224 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5226),uu____5227) ->
            let uu____5248 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____5248 head_match
        | (uu____5249,FStar_Syntax_Syntax.Tm_app (head1,uu____5251)) ->
            let uu____5272 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____5272 head_match
        | uu____5273 ->
            let uu____5278 =
              let uu____5287 = delta_depth_of_term env t11 in
              let uu____5290 = delta_depth_of_term env t21 in
              (uu____5287, uu____5290) in
            MisMatch uu____5278
let head_matches_delta:
  'Auu____5302 .
    FStar_TypeChecker_Env.env ->
      'Auu____5302 ->
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
            let uu____5335 = FStar_Syntax_Util.head_and_args t in
            match uu____5335 with
            | (head1,uu____5353) ->
                let uu____5374 =
                  let uu____5375 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5375.FStar_Syntax_Syntax.n in
                (match uu____5374 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5381 =
                       let uu____5382 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_All.pipe_right uu____5382 FStar_Option.isSome in
                     if uu____5381
                     then
                       let uu____5401 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t in
                       FStar_All.pipe_right uu____5401
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                     else FStar_Pervasives_Native.None
                 | uu____5405 -> FStar_Pervasives_Native.None) in
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
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5508)
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5526 =
                     let uu____5535 = maybe_inline t11 in
                     let uu____5538 = maybe_inline t21 in
                     (uu____5535, uu____5538) in
                   match uu____5526 with
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
                (uu____5575,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5593 =
                     let uu____5602 = maybe_inline t11 in
                     let uu____5605 = maybe_inline t21 in
                     (uu____5602, uu____5605) in
                   match uu____5593 with
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
                let uu____5648 = FStar_TypeChecker_Common.decr_delta_depth d1 in
                (match uu____5648 with
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
                let uu____5671 =
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
                (match uu____5671 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____5695 -> fail r
            | uu____5704 -> success n_delta r t11 t21 in
          aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp[@@deriving show]
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____5737 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____5773 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list[@@deriving show]
let tc_to_string: tc -> Prims.string =
  fun uu___233_5785  ->
    match uu___233_5785 with
    | T (t,uu____5787) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____5803 = FStar_Syntax_Util.type_u () in
      match uu____5803 with
      | (t,uu____5809) ->
          let uu____5810 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____5810
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____5821 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____5821 FStar_Pervasives_Native.fst
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
        let uu____5885 = head_matches env t1 t' in
        match uu____5885 with
        | MisMatch uu____5886 -> false
        | uu____5895 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____5991,imp),T (t2,uu____5994)) -> (t2, imp)
                     | uu____6013 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6080  ->
                    match uu____6080 with
                    | (t2,uu____6094) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6137 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6137 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6212))::tcs2) ->
                       aux
                         (((let uu___257_6247 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___257_6247.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___257_6247.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6265 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___234_6318 =
                 match uu___234_6318 with
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
               let uu____6435 = decompose1 [] bs1 in
               (rebuild, matches, uu____6435))
      | uu____6484 ->
          let rebuild uu___235_6490 =
            match uu___235_6490 with
            | [] -> t1
            | uu____6493 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___236_6524  ->
    match uu___236_6524 with
    | T (t,uu____6526) -> t
    | uu____6535 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___237_6538  ->
    match uu___237_6538 with
    | T (t,uu____6540) -> FStar_Syntax_Syntax.as_arg t
    | uu____6549 -> failwith "Impossible"
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
              | (uu____6655,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____6680 = new_uvar r scope1 k in
                  (match uu____6680 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____6698 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____6715 =
                         let uu____6716 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____6716 in
                       ((T (gi_xs, mk_kind)), uu____6715))
              | (uu____6729,uu____6730,C uu____6731) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____6878 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____6895;
                         FStar_Syntax_Syntax.vars = uu____6896;_})
                        ->
                        let uu____6919 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____6919 with
                         | (T (gi_xs,uu____6943),prob) ->
                             let uu____6953 =
                               let uu____6954 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____6954 in
                             (uu____6953, [prob])
                         | uu____6957 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____6972;
                         FStar_Syntax_Syntax.vars = uu____6973;_})
                        ->
                        let uu____6996 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____6996 with
                         | (T (gi_xs,uu____7020),prob) ->
                             let uu____7030 =
                               let uu____7031 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____7031 in
                             (uu____7030, [prob])
                         | uu____7034 -> failwith "impossible")
                    | (uu____7045,uu____7046,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7048;
                         FStar_Syntax_Syntax.vars = uu____7049;_})
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
                        let uu____7180 =
                          let uu____7189 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____7189 FStar_List.unzip in
                        (match uu____7180 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7243 =
                                 let uu____7244 =
                                   let uu____7247 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____7247 un_T in
                                 let uu____7248 =
                                   let uu____7257 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____7257
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7244;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7248;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7243 in
                             ((C gi_xs), sub_probs))
                    | uu____7266 ->
                        let uu____7279 = sub_prob scope1 args q in
                        (match uu____7279 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____6878 with
                   | (tc,probs) ->
                       let uu____7310 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7373,uu____7374),T
                            (t,uu____7376)) ->
                             let b1 =
                               ((let uu___258_7413 = b in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___258_7413.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___258_7413.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp) in
                             let uu____7414 =
                               let uu____7421 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1 in
                               uu____7421 :: args in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7414)
                         | uu____7456 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____7310 with
                        | (bopt,scope2,args1) ->
                            let uu____7540 = aux scope2 args1 qs2 in
                            (match uu____7540 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____7577 =
                                         let uu____7580 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____7580 in
                                       FStar_Syntax_Util.mk_conj_l uu____7577
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____7603 =
                                         let uu____7606 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____7607 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____7606 :: uu____7607 in
                                       FStar_Syntax_Util.mk_conj_l uu____7603 in
                                 ((FStar_List.append probs sub_probs), (tc ::
                                   tcs), f1)))) in
            aux scope ps qs
type flex_t =
(FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.args)


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
  'Auu____7675 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____7675)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____7675)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___259_7696 = p in
      let uu____7701 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____7702 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___259_7696.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7701;
        FStar_TypeChecker_Common.relation =
          (uu___259_7696.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7702;
        FStar_TypeChecker_Common.element =
          (uu___259_7696.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___259_7696.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___259_7696.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___259_7696.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___259_7696.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___259_7696.FStar_TypeChecker_Common.rank)
      }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7714 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____7714
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____7723 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____7743 = compress_prob wl pr in
        FStar_All.pipe_right uu____7743 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7753 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____7753 with
           | (lh,uu____7773) ->
               let uu____7794 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____7794 with
                | (rh,uu____7814) ->
                    let uu____7835 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7852,FStar_Syntax_Syntax.Tm_uvar uu____7853)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7890,uu____7891)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____7912,FStar_Syntax_Syntax.Tm_uvar uu____7913)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7934,uu____7935)
                          ->
                          let uu____7952 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____7952 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8001 ->
                                    let rank =
                                      let uu____8009 = is_top_level_prob prob in
                                      if uu____8009
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____8011 =
                                      let uu___260_8016 = tp in
                                      let uu____8021 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___260_8016.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___260_8016.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___260_8016.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8021;
                                        FStar_TypeChecker_Common.element =
                                          (uu___260_8016.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___260_8016.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___260_8016.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___260_8016.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___260_8016.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___260_8016.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____8011)))
                      | (uu____8032,FStar_Syntax_Syntax.Tm_uvar uu____8033)
                          ->
                          let uu____8050 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____8050 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8099 ->
                                    let uu____8106 =
                                      let uu___261_8113 = tp in
                                      let uu____8118 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___261_8113.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8118;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___261_8113.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___261_8113.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___261_8113.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___261_8113.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___261_8113.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___261_8113.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___261_8113.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___261_8113.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____8106)))
                      | (uu____8135,uu____8136) -> (rigid_rigid, tp) in
                    (match uu____7835 with
                     | (rank,tp1) ->
                         let uu____8155 =
                           FStar_All.pipe_right
                             (let uu___262_8161 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___262_8161.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___262_8161.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___262_8161.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___262_8161.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___262_8161.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___262_8161.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___262_8161.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___262_8161.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___262_8161.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50) in
                         (rank, uu____8155))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8171 =
            FStar_All.pipe_right
              (let uu___263_8177 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___263_8177.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___263_8177.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___263_8177.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___263_8177.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___263_8177.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___263_8177.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___263_8177.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___263_8177.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___263_8177.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51) in
          (rigid_rigid, uu____8171)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____8232 probs =
      match uu____8232 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8285 = rank wl hd1 in
               (match uu____8285 with
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
    match projectee with | UDeferred _0 -> true | uu____8392 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8404 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8416 -> false
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
                        let uu____8456 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____8456 with
                        | (k,uu____8462) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8472 -> false)))
            | uu____8473 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____8524 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____8524 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____8527 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____8537 =
                     let uu____8538 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____8539 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____8538
                       uu____8539 in
                   UFailed uu____8537)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8559 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8559 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8581 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8581 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____8584 ->
                let uu____8589 =
                  let uu____8590 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____8591 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8590
                    uu____8591 msg in
                UFailed uu____8589 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8592,uu____8593) ->
              let uu____8594 =
                let uu____8595 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8596 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8595 uu____8596 in
              failwith uu____8594
          | (FStar_Syntax_Syntax.U_unknown ,uu____8597) ->
              let uu____8598 =
                let uu____8599 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8600 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8599 uu____8600 in
              failwith uu____8598
          | (uu____8601,FStar_Syntax_Syntax.U_bvar uu____8602) ->
              let uu____8603 =
                let uu____8604 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8605 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8604 uu____8605 in
              failwith uu____8603
          | (uu____8606,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8607 =
                let uu____8608 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____8609 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8608 uu____8609 in
              failwith uu____8607
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8633 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____8633
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____8655 = occurs_univ v1 u3 in
              if uu____8655
              then
                let uu____8656 =
                  let uu____8657 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____8658 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8657 uu____8658 in
                try_umax_components u11 u21 uu____8656
              else
                (let uu____8660 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____8660)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____8680 = occurs_univ v1 u3 in
              if uu____8680
              then
                let uu____8681 =
                  let uu____8682 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____8683 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8682 uu____8683 in
                try_umax_components u11 u21 uu____8681
              else
                (let uu____8685 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____8685)
          | (FStar_Syntax_Syntax.U_max uu____8694,uu____8695) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____8701 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____8701
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8703,FStar_Syntax_Syntax.U_max uu____8704) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____8710 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____8710
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8712,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8713,FStar_Syntax_Syntax.U_name
             uu____8714) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8715) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8716) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8717,FStar_Syntax_Syntax.U_succ
             uu____8718) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8719,FStar_Syntax_Syntax.U_zero
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
      let uu____8805 = bc1 in
      match uu____8805 with
      | (bs1,mk_cod1) ->
          let uu____8846 = bc2 in
          (match uu____8846 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____8916 = FStar_Util.first_N n1 bs in
                 match uu____8916 with
                 | (bs3,rest) ->
                     let uu____8941 = mk_cod rest in (bs3, uu____8941) in
               let l1 = FStar_List.length bs1 in
               let l2 = FStar_List.length bs2 in
               if l1 = l2
               then
                 let uu____8970 =
                   let uu____8977 = mk_cod1 [] in (bs1, uu____8977) in
                 let uu____8980 =
                   let uu____8987 = mk_cod2 [] in (bs2, uu____8987) in
                 (uu____8970, uu____8980)
               else
                 if l1 > l2
                 then
                   (let uu____9029 = curry l2 bs1 mk_cod1 in
                    let uu____9042 =
                      let uu____9049 = mk_cod2 [] in (bs2, uu____9049) in
                    (uu____9029, uu____9042))
                 else
                   (let uu____9065 =
                      let uu____9072 = mk_cod1 [] in (bs1, uu____9072) in
                    let uu____9075 = curry l1 bs2 mk_cod2 in
                    (uu____9065, uu____9075)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____9196 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____9196
       then
         let uu____9197 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9197
       else ());
      (let uu____9199 = next_prob probs in
       match uu____9199 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___264_9220 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___264_9220.wl_deferred);
               ctr = (uu___264_9220.ctr);
               defer_ok = (uu___264_9220.defer_ok);
               smt_ok = (uu___264_9220.smt_ok);
               tcenv = (uu___264_9220.tcenv)
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
                  let uu____9231 = solve_flex_rigid_join env tp probs1 in
                  (match uu____9231 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9236 = solve_rigid_flex_meet env tp probs1 in
                     match uu____9236 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9241,uu____9242) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9259 ->
                let uu____9268 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9327  ->
                          match uu____9327 with
                          | (c,uu____9335,uu____9336) -> c < probs.ctr)) in
                (match uu____9268 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9377 =
                            FStar_List.map
                              (fun uu____9392  ->
                                 match uu____9392 with
                                 | (uu____9403,x,y) -> (x, y))
                              probs.wl_deferred in
                          Success uu____9377
                      | uu____9406 ->
                          let uu____9415 =
                            let uu___265_9416 = probs in
                            let uu____9417 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9438  ->
                                      match uu____9438 with
                                      | (uu____9445,uu____9446,y) -> y)) in
                            {
                              attempting = uu____9417;
                              wl_deferred = rest;
                              ctr = (uu___265_9416.ctr);
                              defer_ok = (uu___265_9416.defer_ok);
                              smt_ok = (uu___265_9416.smt_ok);
                              tcenv = (uu___265_9416.tcenv)
                            } in
                          solve env uu____9415))))
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
            let uu____9453 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____9453 with
            | USolved wl1 ->
                let uu____9455 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____9455
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
                  let uu____9501 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____9501 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9504 -> UFailed "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9516;
                  FStar_Syntax_Syntax.vars = uu____9517;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9520;
                  FStar_Syntax_Syntax.vars = uu____9521;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9535,uu____9536) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9543,FStar_Syntax_Syntax.Tm_uinst uu____9544) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9551 -> USolved wl
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
            ((let uu____9561 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____9561
              then
                let uu____9562 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____9562 msg
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
        (let uu____9571 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____9571
         then
           let uu____9572 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____9572
         else ());
        (let uu____9574 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____9574 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____9636 = head_matches_delta env () t1 t2 in
               match uu____9636 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____9677 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____9726 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____9741 =
                                FStar_Syntax_Subst.compress t11 in
                              let uu____9742 =
                                FStar_Syntax_Subst.compress t21 in
                              (uu____9741, uu____9742)
                          | FStar_Pervasives_Native.None  ->
                              let uu____9747 = FStar_Syntax_Subst.compress t1 in
                              let uu____9748 = FStar_Syntax_Subst.compress t2 in
                              (uu____9747, uu____9748) in
                        (match uu____9726 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____9774 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____9774 in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____9805 =
                                    let uu____9814 =
                                      let uu____9817 =
                                        let uu____9820 =
                                          let uu____9821 =
                                            let uu____9828 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2 in
                                            (x, uu____9828) in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____9821 in
                                        FStar_Syntax_Syntax.mk uu____9820 in
                                      uu____9817 FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos in
                                    let uu____9836 =
                                      let uu____9839 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort in
                                      [uu____9839] in
                                    (uu____9814, uu____9836) in
                                  FStar_Pervasives_Native.Some uu____9805
                              | (uu____9852,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____9854)) ->
                                  let uu____9859 =
                                    let uu____9866 =
                                      let uu____9869 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11 in
                                      [uu____9869] in
                                    (t11, uu____9866) in
                                  FStar_Pervasives_Native.Some uu____9859
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____9879),uu____9880) ->
                                  let uu____9885 =
                                    let uu____9892 =
                                      let uu____9895 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21 in
                                      [uu____9895] in
                                    (t21, uu____9892) in
                                  FStar_Pervasives_Native.Some uu____9885
                              | uu____9904 ->
                                  let uu____9909 =
                                    FStar_Syntax_Util.head_and_args t11 in
                                  (match uu____9909 with
                                   | (head1,uu____9933) ->
                                       let uu____9954 =
                                         let uu____9955 =
                                           FStar_Syntax_Util.un_uinst head1 in
                                         uu____9955.FStar_Syntax_Syntax.n in
                                       (match uu____9954 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____9966;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____9968;_}
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
                                        | uu____9975 ->
                                            FStar_Pervasives_Native.None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____9988) ->
                  let uu____10013 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___238_10039  ->
                            match uu___238_10039 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10046 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs in
                                     (match uu____10046 with
                                      | (u',uu____10062) ->
                                          let uu____10083 =
                                            let uu____10084 = whnf env u' in
                                            uu____10084.FStar_Syntax_Syntax.n in
                                          (match uu____10083 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10088) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10113 -> false))
                                 | uu____10114 -> false)
                            | uu____10117 -> false)) in
                  (match uu____10013 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10151 tps =
                         match uu____10151 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10199 =
                                    let uu____10208 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs in
                                    disjoin bound uu____10208 in
                                  (match uu____10199 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10243 -> FStar_Pervasives_Native.None) in
                       let uu____10252 =
                         let uu____10261 =
                           let uu____10268 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (uu____10268, []) in
                         make_lower_bound uu____10261 lower_bounds in
                       (match uu____10252 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10280 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10280
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
                            ((let uu____10300 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____10300
                              then
                                let wl' =
                                  let uu___266_10302 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___266_10302.wl_deferred);
                                    ctr = (uu___266_10302.ctr);
                                    defer_ok = (uu___266_10302.defer_ok);
                                    smt_ok = (uu___266_10302.smt_ok);
                                    tcenv = (uu___266_10302.tcenv)
                                  } in
                                let uu____10303 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10303
                              else ());
                             (let uu____10305 =
                                solve_t env eq_prob
                                  (let uu___267_10307 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___267_10307.wl_deferred);
                                     ctr = (uu___267_10307.ctr);
                                     defer_ok = (uu___267_10307.defer_ok);
                                     smt_ok = (uu___267_10307.smt_ok);
                                     tcenv = (uu___267_10307.tcenv)
                                   }) in
                              match uu____10305 with
                              | Success uu____10310 ->
                                  let wl1 =
                                    let uu___268_10312 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___268_10312.wl_deferred);
                                      ctr = (uu___268_10312.ctr);
                                      defer_ok = (uu___268_10312.defer_ok);
                                      smt_ok = (uu___268_10312.smt_ok);
                                      tcenv = (uu___268_10312.tcenv)
                                    } in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1 in
                                  let uu____10314 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10319 -> FStar_Pervasives_Native.None))))
              | uu____10320 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10329 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____10329
         then
           let uu____10330 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10330
         else ());
        (let uu____10332 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____10332 with
         | (u,args) ->
             let uu____10371 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____10371 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____10412 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____10412 with
                    | (h1,args1) ->
                        let uu____10453 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____10453 with
                         | (h2,uu____10473) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____10500 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____10500
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____10518 =
                                          let uu____10521 =
                                            let uu____10522 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____10522 in
                                          [uu____10521] in
                                        FStar_Pervasives_Native.Some
                                          uu____10518))
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
                                       (let uu____10555 =
                                          let uu____10558 =
                                            let uu____10559 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements" in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____10559 in
                                          [uu____10558] in
                                        FStar_Pervasives_Native.Some
                                          uu____10555))
                                  else FStar_Pervasives_Native.None
                              | uu____10573 -> FStar_Pervasives_Native.None)) in
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
                             let uu____10663 =
                               let uu____10672 =
                                 let uu____10675 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21 in
                                 FStar_Syntax_Util.refine x1 uu____10675 in
                               (uu____10672, m1) in
                             FStar_Pervasives_Native.Some uu____10663)
                    | (uu____10688,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____10690)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____10738),uu____10739) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____10786 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10839) ->
                       let uu____10864 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___239_10890  ->
                                 match uu___239_10890 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____10897 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs in
                                          (match uu____10897 with
                                           | (u',uu____10913) ->
                                               let uu____10934 =
                                                 let uu____10935 =
                                                   whnf env u' in
                                                 uu____10935.FStar_Syntax_Syntax.n in
                                               (match uu____10934 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____10939) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____10964 -> false))
                                      | uu____10965 -> false)
                                 | uu____10968 -> false)) in
                       (match uu____10864 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11006 tps =
                              match uu____11006 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11068 =
                                         let uu____11079 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs in
                                         conjoin bound uu____11079 in
                                       (match uu____11068 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11130 ->
                                       FStar_Pervasives_Native.None) in
                            let uu____11141 =
                              let uu____11152 =
                                let uu____11161 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (uu____11161, []) in
                              make_upper_bound uu____11152 upper_bounds in
                            (match uu____11141 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11175 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11175
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
                                 ((let uu____11201 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____11201
                                   then
                                     let wl' =
                                       let uu___269_11203 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___269_11203.wl_deferred);
                                         ctr = (uu___269_11203.ctr);
                                         defer_ok = (uu___269_11203.defer_ok);
                                         smt_ok = (uu___269_11203.smt_ok);
                                         tcenv = (uu___269_11203.tcenv)
                                       } in
                                     let uu____11204 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11204
                                   else ());
                                  (let uu____11206 =
                                     solve_t env eq_prob
                                       (let uu___270_11208 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___270_11208.wl_deferred);
                                          ctr = (uu___270_11208.ctr);
                                          defer_ok =
                                            (uu___270_11208.defer_ok);
                                          smt_ok = (uu___270_11208.smt_ok);
                                          tcenv = (uu___270_11208.tcenv)
                                        }) in
                                   match uu____11206 with
                                   | Success uu____11211 ->
                                       let wl1 =
                                         let uu___271_11213 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___271_11213.wl_deferred);
                                           ctr = (uu___271_11213.ctr);
                                           defer_ok =
                                             (uu___271_11213.defer_ok);
                                           smt_ok = (uu___271_11213.smt_ok);
                                           tcenv = (uu___271_11213.tcenv)
                                         } in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1 in
                                       let uu____11215 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11220 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11221 -> failwith "Impossible: Not a flex-rigid")))
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
                    ((let uu____11296 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____11296
                      then
                        let uu____11297 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11297
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___272_11351 = hd1 in
                      let uu____11352 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___272_11351.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___272_11351.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11352
                      } in
                    let hd21 =
                      let uu___273_11356 = hd2 in
                      let uu____11357 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___273_11356.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___273_11356.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11357
                      } in
                    let prob =
                      let uu____11361 =
                        let uu____11366 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11366 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____11361 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____11377 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11377 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____11381 =
                      aux (FStar_List.append scope [(hd12, imp)]) env2 subst2
                        xs1 ys1 in
                    (match uu____11381 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11419 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____11424 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____11419 uu____11424 in
                         ((let uu____11434 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____11434
                           then
                             let uu____11435 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____11436 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11435 uu____11436
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11459 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____11469 = aux scope env [] bs1 bs2 in
              match uu____11469 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____11493 = compress_tprob wl problem in
        solve_t' env uu____11493 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____11526 = head_matches_delta env1 wl1 t1 t2 in
          match uu____11526 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____11557,uu____11558) ->
                   let rec may_relate head3 =
                     let uu____11583 =
                       let uu____11584 = FStar_Syntax_Subst.compress head3 in
                       uu____11584.FStar_Syntax_Syntax.n in
                     match uu____11583 with
                     | FStar_Syntax_Syntax.Tm_name uu____11587 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____11588 -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____11611;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_equational ;
                           FStar_Syntax_Syntax.fv_qual = uu____11612;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____11615;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_abstract uu____11616;
                           FStar_Syntax_Syntax.fv_qual = uu____11617;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____11621,uu____11622) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____11664) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____11670) ->
                         may_relate t
                     | uu____11675 -> false in
                   let uu____11676 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok in
                   if uu____11676
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
                                let uu____11693 =
                                  let uu____11694 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____11694 t21 in
                                FStar_Syntax_Util.mk_forall u_x x uu____11693 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let uu____11696 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1 in
                     solve env1 uu____11696
                   else
                     (let uu____11698 =
                        let uu____11699 =
                          FStar_Syntax_Print.term_to_string head1 in
                        let uu____11700 =
                          FStar_Syntax_Print.term_to_string head2 in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____11699 uu____11700 in
                      giveup env1 uu____11698 orig)
               | (uu____11701,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___274_11715 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___274_11715.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___274_11715.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___274_11715.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___274_11715.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___274_11715.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___274_11715.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___274_11715.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___274_11715.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____11716,FStar_Pervasives_Native.None ) ->
                   ((let uu____11728 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____11728
                     then
                       let uu____11729 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____11730 = FStar_Syntax_Print.tag_of_term t1 in
                       let uu____11731 = FStar_Syntax_Print.term_to_string t2 in
                       let uu____11732 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____11729
                         uu____11730 uu____11731 uu____11732
                     else ());
                    (let uu____11734 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____11734 with
                     | (head11,args1) ->
                         let uu____11771 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____11771 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____11825 =
                                  let uu____11826 =
                                    FStar_Syntax_Print.term_to_string head11 in
                                  let uu____11827 = args_to_string args1 in
                                  let uu____11828 =
                                    FStar_Syntax_Print.term_to_string head21 in
                                  let uu____11829 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____11826 uu____11827 uu____11828
                                    uu____11829 in
                                giveup env1 uu____11825 orig
                              else
                                (let uu____11831 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____11837 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      uu____11837 = FStar_Syntax_Util.Equal) in
                                 if uu____11831
                                 then
                                   let uu____11838 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1 in
                                   match uu____11838 with
                                   | USolved wl2 ->
                                       let uu____11840 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2 in
                                       solve env1 uu____11840
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____11844 =
                                      base_and_refinement env1 t1 in
                                    match uu____11844 with
                                    | (base1,refinement1) ->
                                        let uu____11869 =
                                          base_and_refinement env1 t2 in
                                        (match uu____11869 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____11926 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____11926 with
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
                                                           (fun uu____11948 
                                                              ->
                                                              fun uu____11949
                                                                 ->
                                                                match 
                                                                  (uu____11948,
                                                                    uu____11949)
                                                                with
                                                                | ((a,uu____11967),
                                                                   (a',uu____11969))
                                                                    ->
                                                                    let uu____11978
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
                                                                    uu____11978)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____11988 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____11988 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____11994 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___275_12030 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___275_12030.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___275_12030.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___275_12030.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___275_12030.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___275_12030.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___275_12030.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___275_12030.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___275_12030.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let force_quasi_pattern xs_opt uu____12069 =
          match uu____12069 with
          | (t,u,k,args) ->
              let rec aux pat_args pattern_vars pattern_var_set seen_formals
                formals res_t args1 =
                match (formals, args1) with
                | ([],[]) ->
                    let pat_args1 =
                      FStar_All.pipe_right (FStar_List.rev pat_args)
                        (FStar_List.map
                           (fun uu____12285  ->
                              match uu____12285 with
                              | (x,imp) ->
                                  let uu____12296 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  (uu____12296, imp))) in
                    let pattern_vars1 = FStar_List.rev pattern_vars in
                    let kk =
                      let uu____12309 = FStar_Syntax_Util.type_u () in
                      match uu____12309 with
                      | (t1,uu____12315) ->
                          let uu____12316 =
                            new_uvar t1.FStar_Syntax_Syntax.pos pattern_vars1
                              t1 in
                          FStar_Pervasives_Native.fst uu____12316 in
                    let uu____12321 =
                      new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk in
                    (match uu____12321 with
                     | (t',tm_u1) ->
                         let uu____12334 = destruct_flex_t t' in
                         (match uu____12334 with
                          | (uu____12371,u1,k1,uu____12374) ->
                              let all_formals = FStar_List.rev seen_formals in
                              let k2 =
                                let uu____12433 =
                                  FStar_Syntax_Syntax.mk_Total res_t in
                                FStar_Syntax_Util.arrow all_formals
                                  uu____12433 in
                              let sol =
                                let uu____12437 =
                                  let uu____12446 = u_abs k2 all_formals t' in
                                  ((u, k2), uu____12446) in
                                TERM uu____12437 in
                              let t_app =
                                FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args1
                                  FStar_Pervasives_Native.None
                                  t.FStar_Syntax_Syntax.pos in
                              FStar_Pervasives_Native.Some
                                (sol, (t_app, u1, k1, pat_args1))))
                | (formal::formals1,hd1::tl1) ->
                    let uu____12582 = pat_var_opt env pat_args hd1 in
                    (match uu____12582 with
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
                                    (fun uu____12645  ->
                                       match uu____12645 with
                                       | (x,uu____12651) ->
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
                            let uu____12666 =
                              let uu____12667 =
                                FStar_Util.set_is_subset_of fvs
                                  pattern_var_set in
                              Prims.op_Negation uu____12667 in
                            if uu____12666
                            then
                              aux pat_args pattern_vars pattern_var_set
                                (formal :: seen_formals) formals1 res_t tl1
                            else
                              (let uu____12679 =
                                 FStar_Util.set_add
                                   (FStar_Pervasives_Native.fst formal)
                                   pattern_var_set in
                               aux (y :: pat_args) (formal :: pattern_vars)
                                 uu____12679 (formal :: seen_formals)
                                 formals1 res_t tl1)))
                | ([],uu____12694::uu____12695) ->
                    let uu____12726 =
                      let uu____12739 =
                        FStar_TypeChecker_Normalize.unfold_whnf env res_t in
                      FStar_Syntax_Util.arrow_formals uu____12739 in
                    (match uu____12726 with
                     | (more_formals,res_t1) ->
                         (match more_formals with
                          | [] -> FStar_Pervasives_Native.None
                          | uu____12778 ->
                              aux pat_args pattern_vars pattern_var_set
                                seen_formals more_formals res_t1 args1))
                | (uu____12785::uu____12786,[]) ->
                    FStar_Pervasives_Native.None in
              let uu____12821 =
                let uu____12834 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k in
                FStar_Syntax_Util.arrow_formals uu____12834 in
              (match uu____12821 with
               | (all_formals,res_t) ->
                   let uu____12859 = FStar_Syntax_Syntax.new_bv_set () in
                   aux [] [] uu____12859 [] all_formals res_t args) in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____12893 = lhs in
          match uu____12893 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____12903 ->
                    let uu____12904 = sn_binders env1 pat_vars1 in
                    u_abs k_uv uu____12904 rhs in
              let wl2 =
                solve_prob orig FStar_Pervasives_Native.None
                  [TERM ((uv, k_uv), sol)] wl1 in
              solve env1 wl2 in
        let imitate orig env1 wl1 p =
          let uu____12927 = p in
          match uu____12927 with
          | (((u,k),xs,c),ps,(h,uu____12938,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13020 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____13020 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13043 = h gs_xs in
                     let uu____13044 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57) in
                     FStar_Syntax_Util.abs xs1 uu____13043 uu____13044 in
                   ((let uu____13050 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____13050
                     then
                       let uu____13051 =
                         let uu____13054 =
                           let uu____13055 =
                             FStar_List.map tc_to_string gs_xs in
                           FStar_All.pipe_right uu____13055
                             (FStar_String.concat "\n\t") in
                         let uu____13060 =
                           let uu____13063 =
                             FStar_Syntax_Print.binders_to_string ", " xs1 in
                           let uu____13064 =
                             let uu____13067 =
                               FStar_Syntax_Print.comp_to_string c in
                             let uu____13068 =
                               let uu____13071 =
                                 FStar_Syntax_Print.term_to_string im in
                               let uu____13072 =
                                 let uu____13075 =
                                   FStar_Syntax_Print.tag_of_term im in
                                 let uu____13076 =
                                   let uu____13079 =
                                     let uu____13080 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs in
                                     FStar_All.pipe_right uu____13080
                                       (FStar_String.concat ", ") in
                                   let uu____13085 =
                                     let uu____13088 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula in
                                     [uu____13088] in
                                   uu____13079 :: uu____13085 in
                                 uu____13075 :: uu____13076 in
                               uu____13071 :: uu____13072 in
                             uu____13067 :: uu____13068 in
                           uu____13063 :: uu____13064 in
                         uu____13054 :: uu____13060 in
                       FStar_Util.print
                         "Imitating gs_xs=%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13051
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___240_13109 =
          match uu___240_13109 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____13141 = p in
          match uu____13141 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____13232 = FStar_List.nth ps i in
              (match uu____13232 with
               | (pi,uu____13236) ->
                   let uu____13241 = FStar_List.nth xs i in
                   (match uu____13241 with
                    | (xi,uu____13253) ->
                        let rec gs k =
                          let uu____13266 =
                            let uu____13279 =
                              FStar_TypeChecker_Normalize.unfold_whnf env1 k in
                            FStar_Syntax_Util.arrow_formals uu____13279 in
                          match uu____13266 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____13354)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____13367 = new_uvar r xs k_a in
                                    (match uu____13367 with
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
                                         let uu____13389 = aux subst2 tl1 in
                                         (match uu____13389 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____13416 =
                                                let uu____13419 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____13419 :: gi_xs' in
                                              let uu____13420 =
                                                let uu____13423 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____13423 :: gi_ps' in
                                              (uu____13416, uu____13420))) in
                              aux [] bs in
                        let uu____13428 =
                          let uu____13429 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____13429 in
                        if uu____13428
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____13433 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____13433 with
                           | (g_xs,uu____13445) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____13456 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____13457 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_58  ->
                                        FStar_Pervasives_Native.Some _0_58) in
                                 FStar_Syntax_Util.abs xs uu____13456
                                   uu____13457 in
                               let sub1 =
                                 let uu____13463 =
                                   let uu____13468 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____13471 =
                                     let uu____13474 =
                                       FStar_List.map
                                         (fun uu____13489  ->
                                            match uu____13489 with
                                            | (uu____13498,uu____13499,y) ->
                                                y) qs in
                                     FStar_All.pipe_left h uu____13474 in
                                   mk_problem (p_scope orig) orig uu____13468
                                     (p_rel orig) uu____13471
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____13463 in
                               ((let uu____13514 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____13514
                                 then
                                   let uu____13515 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____13516 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____13515 uu____13516
                                 else ());
                                (let wl2 =
                                   let uu____13519 =
                                     let uu____13522 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____13522 in
                                   solve_prob orig uu____13519
                                     [TERM (u, proj)] wl1 in
                                 let uu____13531 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____13531))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____13562 = lhs in
          match uu____13562 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____13598 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____13598 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____13631 =
                        let uu____13678 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____13678) in
                      FStar_Pervasives_Native.Some uu____13631
                    else
                      (let rec elim k args =
                         let k1 =
                           FStar_TypeChecker_Normalize.unfold_whnf env k in
                         let uu____13822 =
                           let uu____13829 =
                             let uu____13830 = FStar_Syntax_Subst.compress k1 in
                             uu____13830.FStar_Syntax_Syntax.n in
                           (uu____13829, args) in
                         match uu____13822 with
                         | (uu____13841,[]) ->
                             let uu____13844 =
                               let uu____13855 =
                                 FStar_Syntax_Syntax.mk_Total k1 in
                               ([], uu____13855) in
                             FStar_Pervasives_Native.Some uu____13844
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____13876,uu____13877) ->
                             let uu____13898 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____13898 with
                              | (uv1,uv_args) ->
                                  let uu____13941 =
                                    let uu____13942 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____13942.FStar_Syntax_Syntax.n in
                                  (match uu____13941 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____13952) ->
                                       let uu____13977 =
                                         pat_vars env [] uv_args in
                                       (match uu____13977 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14004  ->
                                                      let uu____14005 =
                                                        let uu____14006 =
                                                          let uu____14007 =
                                                            let uu____14012 =
                                                              let uu____14013
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14013
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14012 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14007 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14006 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14005)) in
                                            let c1 =
                                              let uu____14023 =
                                                let uu____14024 =
                                                  let uu____14029 =
                                                    let uu____14030 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14030
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14029 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14024 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14023 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14043 =
                                                let uu____14046 =
                                                  let uu____14047 =
                                                    let uu____14050 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14050
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14047 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14046 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14043 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14068 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14073,uu____14074) ->
                             let uu____14093 =
                               FStar_Syntax_Util.head_and_args k1 in
                             (match uu____14093 with
                              | (uv1,uv_args) ->
                                  let uu____14136 =
                                    let uu____14137 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____14137.FStar_Syntax_Syntax.n in
                                  (match uu____14136 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14147) ->
                                       let uu____14172 =
                                         pat_vars env [] uv_args in
                                       (match uu____14172 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14199  ->
                                                      let uu____14200 =
                                                        let uu____14201 =
                                                          let uu____14202 =
                                                            let uu____14207 =
                                                              let uu____14208
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____14208
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14207 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14202 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14201 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14200)) in
                                            let c1 =
                                              let uu____14218 =
                                                let uu____14219 =
                                                  let uu____14224 =
                                                    let uu____14225 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14225
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14224 in
                                                FStar_Pervasives_Native.fst
                                                  uu____14219 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14218 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____14238 =
                                                let uu____14241 =
                                                  let uu____14242 =
                                                    let uu____14245 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____14245
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14242 in
                                                FStar_Pervasives_Native.Some
                                                  uu____14241 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14238 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14263 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____14270) ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____14311 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____14311
                                 (fun _0_61  ->
                                    FStar_Pervasives_Native.Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____14347 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____14347 with
                                  | (args1,rest) ->
                                      let uu____14376 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____14376 with
                                       | (xs2,c2) ->
                                           let uu____14389 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____14389
                                             (fun uu____14413  ->
                                                match uu____14413 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____14453 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____14453 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k1.FStar_Syntax_Syntax.pos in
                                      let uu____14521 =
                                        let uu____14526 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____14526 in
                                      FStar_All.pipe_right uu____14521
                                        (fun _0_62  ->
                                           FStar_Pervasives_Native.Some _0_62))
                         | uu____14541 ->
                             let uu____14548 =
                               let uu____14549 =
                                 let uu____14554 =
                                   let uu____14555 =
                                     FStar_Syntax_Print.uvar_to_string uv in
                                   let uu____14556 =
                                     FStar_Syntax_Print.term_to_string k1 in
                                   let uu____14557 =
                                     FStar_Syntax_Print.term_to_string k_uv in
                                   FStar_Util.format3
                                     "Impossible: ill-typed application %s : %s\n\t%s"
                                     uu____14555 uu____14556 uu____14557 in
                                 (uu____14554, (t1.FStar_Syntax_Syntax.pos)) in
                               FStar_Errors.Error uu____14549 in
                             FStar_Exn.raise uu____14548 in
                       let uu____14564 = elim k_uv ps in
                       FStar_Util.bind_opt uu____14564
                         (fun uu____14619  ->
                            match uu____14619 with
                            | (xs1,c1) ->
                                let uu____14668 =
                                  let uu____14709 = decompose env t2 in
                                  (((uv, k_uv), xs1, c1), ps, uu____14709) in
                                FStar_Pervasives_Native.Some uu____14668)) in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail uu____14830 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig in
                let rec try_project st i =
                  if i >= n1
                  then fail ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction () in
                     let uu____14846 = project orig env wl1 i st in
                     match uu____14846 with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some (Failed uu____14860) ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some sol -> sol) in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt in
                  let tx = FStar_Syntax_Unionfind.new_transaction () in
                  let uu____14875 = imitate orig env wl1 st in
                  match uu____14875 with
                  | Failed uu____14880 ->
                      (FStar_Syntax_Unionfind.rollback tx;
                       try_project st (Prims.parse_int "0"))
                  | sol -> sol
                else fail () in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____14911 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1 in
                match uu____14911 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let tx = FStar_Syntax_Unionfind.new_transaction () in
                    let wl2 = extend_solution (p_pid orig) [sol] wl1 in
                    let uu____14936 =
                      let uu____14937 =
                        FStar_TypeChecker_Common.as_tprob orig in
                      solve_t env uu____14937 wl2 in
                    (match uu____14936 with
                     | Failed uu____14938 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 lhs1 rhs stopt)
                     | sol1 -> sol1) in
              let check_head fvs1 t21 =
                let uu____14956 = FStar_Syntax_Util.head_and_args t21 in
                match uu____14956 with
                | (hd1,uu____14972) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____14993 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15006 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15007 -> true
                     | uu____15024 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____15028 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____15028
                         then true
                         else
                           ((let uu____15031 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____15031
                             then
                               let uu____15032 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s\n"
                                 uu____15032
                             else ());
                            false)) in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let lhs1 = (t11, uv, k_uv, args_lhs) in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____15052 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____15052 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15065 =
                            let uu____15066 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____15066 in
                          giveup_or_defer1 orig uu____15065
                        else
                          (let uu____15068 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____15068
                           then
                             let uu____15069 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____15069
                              then
                                let uu____15070 = subterms args_lhs in
                                imitate' orig env wl1 uu____15070
                              else
                                ((let uu____15075 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____15075
                                  then
                                    let uu____15076 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____15077 = names_to_string fvs1 in
                                    let uu____15078 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15076 uu____15077 uu____15078
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
                               (let uu____15082 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____15082
                                then
                                  ((let uu____15084 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____15084
                                    then
                                      let uu____15085 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____15086 = names_to_string fvs1 in
                                      let uu____15087 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                        uu____15085 uu____15086 uu____15087
                                    else ());
                                   (let uu____15089 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) lhs1 t21
                                      uu____15089))
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
                     (let uu____15100 =
                        let uu____15101 = FStar_Syntax_Free.names t1 in
                        check_head uu____15101 t2 in
                      if uu____15100
                      then
                        let n_args_lhs = FStar_List.length args_lhs in
                        ((let uu____15112 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____15112
                          then
                            let uu____15113 =
                              FStar_Syntax_Print.term_to_string t1 in
                            let uu____15114 =
                              FStar_Util.string_of_int n_args_lhs in
                            FStar_Util.print2
                              "Not a pattern (%s) ... (lhs has %s args)\n"
                              uu____15113 uu____15114
                          else ());
                         (let uu____15122 = subterms args_lhs in
                          pattern_eq_imitate_or_project n_args_lhs
                            (FStar_Pervasives_Native.fst lhs) t2 uu____15122))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let solve_both_pats wl1 uu____15199 uu____15200 r =
               match (uu____15199, uu____15200) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____15398 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____15398
                   then
                     let uu____15399 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____15399
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____15423 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____15423
                       then
                         let uu____15424 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____15425 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____15426 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____15427 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____15428 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____15424 uu____15425 uu____15426 uu____15427
                           uu____15428
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____15488 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____15488 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____15502 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____15502 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____15556 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____15556 in
                                  let uu____15559 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____15559 k3)
                           else
                             (let uu____15563 =
                                let uu____15564 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____15565 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____15566 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____15564 uu____15565 uu____15566 in
                              failwith uu____15563) in
                       let uu____15567 =
                         let uu____15574 =
                           let uu____15587 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____15587 in
                         match uu____15574 with
                         | (bs,k1') ->
                             let uu____15612 =
                               let uu____15625 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____15625 in
                             (match uu____15612 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____15653 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____15653 in
                                  let uu____15662 =
                                    let uu____15667 =
                                      let uu____15668 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____15668.FStar_Syntax_Syntax.n in
                                    let uu____15671 =
                                      let uu____15672 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____15672.FStar_Syntax_Syntax.n in
                                    (uu____15667, uu____15671) in
                                  (match uu____15662 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____15681,uu____15682) ->
                                       (k1'_xs, [sub_prob])
                                   | (uu____15685,FStar_Syntax_Syntax.Tm_type
                                      uu____15686) -> (k2'_ys, [sub_prob])
                                   | uu____15689 ->
                                       let uu____15694 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____15694 with
                                        | (t,uu____15706) ->
                                            let uu____15707 = new_uvar r zs t in
                                            (match uu____15707 with
                                             | (k_zs,uu____15719) ->
                                                 let kprob =
                                                   let uu____15721 =
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
                                                          _0_64) uu____15721 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____15567 with
                       | (k_u',sub_probs) ->
                           let uu____15738 =
                             let uu____15749 =
                               let uu____15750 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____15750 in
                             let uu____15759 =
                               let uu____15762 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____15762 in
                             let uu____15765 =
                               let uu____15768 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____15768 in
                             (uu____15749, uu____15759, uu____15765) in
                           (match uu____15738 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____15787 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____15787 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____15806 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____15806
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____15810 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____15810 with
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
             let solve_one_pat uu____15863 uu____15864 =
               match (uu____15863, uu____15864) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____15982 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____15982
                     then
                       let uu____15983 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____15984 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____15983 uu____15984
                     else ());
                    (let uu____15986 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____15986
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16005  ->
                              fun uu____16006  ->
                                match (uu____16005, uu____16006) with
                                | ((a,uu____16024),(t21,uu____16026)) ->
                                    let uu____16035 =
                                      let uu____16040 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____16040
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____16035
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2 in
                       let guard =
                         let uu____16046 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____16046 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____16061 = occurs_check env wl (u1, k1) t21 in
                        match uu____16061 with
                        | (occurs_ok,uu____16069) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____16077 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____16077
                            then
                              let sol =
                                let uu____16079 =
                                  let uu____16088 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____16088) in
                                TERM uu____16079 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____16095 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____16095
                               then
                                 let uu____16096 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____16096 with
                                 | FStar_Pervasives_Native.None  ->
                                     giveup_or_defer1 orig
                                       "flex-flex constraint"
                                 | FStar_Pervasives_Native.Some
                                     (sol,(uu____16120,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____16146 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____16146
                                       then
                                         let uu____16147 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16147
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16154 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____16156 = lhs in
             match uu____16156 with
             | (t1,u1,k1,args1) ->
                 let uu____16161 = rhs in
                 (match uu____16161 with
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
                       | uu____16201 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16211 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____16211 with
                              | FStar_Pervasives_Native.None  ->
                                  giveup env
                                    "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                    orig
                              | FStar_Pervasives_Native.Some
                                  (sol,uu____16229) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____16236 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____16236
                                    then
                                      let uu____16237 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16237
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16244 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____16246 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____16246
        then
          let uu____16247 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____16247
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____16251 = FStar_Util.physical_equality t1 t2 in
           if uu____16251
           then
             let uu____16252 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____16252
           else
             ((let uu____16255 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____16255
               then
                 let uu____16256 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____16256
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_ascribed uu____16259,uu____16260) ->
                   let uu____16287 =
                     let uu___276_16288 = problem in
                     let uu____16289 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___276_16288.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16289;
                       FStar_TypeChecker_Common.relation =
                         (uu___276_16288.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___276_16288.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___276_16288.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___276_16288.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___276_16288.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___276_16288.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___276_16288.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___276_16288.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16287 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____16290,uu____16291) ->
                   let uu____16298 =
                     let uu___276_16299 = problem in
                     let uu____16300 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___276_16299.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16300;
                       FStar_TypeChecker_Common.relation =
                         (uu___276_16299.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___276_16299.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___276_16299.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___276_16299.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___276_16299.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___276_16299.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___276_16299.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___276_16299.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16298 wl
               | (uu____16301,FStar_Syntax_Syntax.Tm_ascribed uu____16302) ->
                   let uu____16329 =
                     let uu___277_16330 = problem in
                     let uu____16331 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___277_16330.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___277_16330.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___277_16330.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16331;
                       FStar_TypeChecker_Common.element =
                         (uu___277_16330.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___277_16330.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___277_16330.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___277_16330.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___277_16330.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___277_16330.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16329 wl
               | (uu____16332,FStar_Syntax_Syntax.Tm_meta uu____16333) ->
                   let uu____16340 =
                     let uu___277_16341 = problem in
                     let uu____16342 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___277_16341.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___277_16341.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___277_16341.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16342;
                       FStar_TypeChecker_Common.element =
                         (uu___277_16341.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___277_16341.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___277_16341.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___277_16341.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___277_16341.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___277_16341.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16340 wl
               | (FStar_Syntax_Syntax.Tm_bvar uu____16343,uu____16344) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____16345,FStar_Syntax_Syntax.Tm_bvar uu____16346) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___241_16401 =
                     match uu___241_16401 with
                     | [] -> c
                     | bs ->
                         let uu____16423 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____16423 in
                   let uu____16432 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____16432 with
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
                                   let uu____16574 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____16574
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____16576 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____16576))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___242_16652 =
                     match uu___242_16652 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____16686 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____16686 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____16822 =
                                   let uu____16827 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____16828 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____16827
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____16828 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____16822))
               | (FStar_Syntax_Syntax.Tm_abs uu____16833,uu____16834) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____16859 -> true
                     | uu____16876 -> false in
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
                       (let uu____16923 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___278_16931 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___278_16931.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___278_16931.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___278_16931.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___278_16931.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___278_16931.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___278_16931.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___278_16931.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___278_16931.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___278_16931.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___278_16931.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___278_16931.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___278_16931.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___278_16931.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___278_16931.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___278_16931.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___278_16931.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___278_16931.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___278_16931.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___278_16931.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___278_16931.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___278_16931.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___278_16931.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___278_16931.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___278_16931.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___278_16931.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___278_16931.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___278_16931.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___278_16931.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___278_16931.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___278_16931.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___278_16931.FStar_TypeChecker_Env.dep_graph)
                             }) t in
                        match uu____16923 with
                        | (uu____16934,ty,uu____16936) ->
                            let uu____16937 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____16937) in
                   let uu____16938 =
                     let uu____16955 = maybe_eta t1 in
                     let uu____16962 = maybe_eta t2 in
                     (uu____16955, uu____16962) in
                   (match uu____16938 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___279_17004 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___279_17004.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___279_17004.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___279_17004.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___279_17004.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___279_17004.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___279_17004.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___279_17004.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___279_17004.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17027 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17027
                        then
                          let uu____17028 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17028 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___280_17043 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___280_17043.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___280_17043.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___280_17043.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___280_17043.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___280_17043.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___280_17043.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___280_17043.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___280_17043.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17067 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17067
                        then
                          let uu____17068 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17068 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___280_17083 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___280_17083.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___280_17083.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___280_17083.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___280_17083.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___280_17083.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___280_17083.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___280_17083.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___280_17083.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17087 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17104,FStar_Syntax_Syntax.Tm_abs uu____17105) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17130 -> true
                     | uu____17147 -> false in
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
                       (let uu____17194 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___278_17202 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___278_17202.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___278_17202.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___278_17202.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___278_17202.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___278_17202.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___278_17202.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___278_17202.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___278_17202.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___278_17202.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___278_17202.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___278_17202.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___278_17202.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___278_17202.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___278_17202.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___278_17202.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___278_17202.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___278_17202.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___278_17202.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___278_17202.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___278_17202.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___278_17202.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___278_17202.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___278_17202.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___278_17202.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___278_17202.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___278_17202.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___278_17202.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___278_17202.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___278_17202.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___278_17202.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___278_17202.FStar_TypeChecker_Env.dep_graph)
                             }) t in
                        match uu____17194 with
                        | (uu____17205,ty,uu____17207) ->
                            let uu____17208 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17208) in
                   let uu____17209 =
                     let uu____17226 = maybe_eta t1 in
                     let uu____17233 = maybe_eta t2 in
                     (uu____17226, uu____17233) in
                   (match uu____17209 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___279_17275 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___279_17275.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___279_17275.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___279_17275.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___279_17275.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___279_17275.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___279_17275.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___279_17275.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___279_17275.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17298 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17298
                        then
                          let uu____17299 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17299 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___280_17314 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___280_17314.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___280_17314.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___280_17314.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___280_17314.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___280_17314.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___280_17314.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___280_17314.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___280_17314.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17338 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17338
                        then
                          let uu____17339 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17339 t_abs wl
                        else
                          (let t11 = force_eta t1 in
                           let t21 = force_eta t2 in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___280_17354 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___280_17354.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___280_17354.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___280_17354.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___280_17354.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___280_17354.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___280_17354.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___280_17354.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___280_17354.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17358 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____17375,FStar_Syntax_Syntax.Tm_refine uu____17376) ->
                   let uu____17389 = as_refinement env wl t1 in
                   (match uu____17389 with
                    | (x1,phi1) ->
                        let uu____17396 = as_refinement env wl t2 in
                        (match uu____17396 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____17404 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____17404 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____17442 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____17442
                                 (guard_on_element wl problem x11) in
                             let fallback uu____17446 =
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
                                 let uu____17452 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____17452 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____17461 =
                                   let uu____17466 =
                                     let uu____17467 =
                                       let uu____17474 =
                                         FStar_Syntax_Syntax.mk_binder x11 in
                                       [uu____17474] in
                                     FStar_List.append (p_scope orig)
                                       uu____17467 in
                                   mk_problem uu____17466 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____17461 in
                               let uu____17483 =
                                 solve env1
                                   (let uu___281_17485 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___281_17485.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___281_17485.smt_ok);
                                      tcenv = (uu___281_17485.tcenv)
                                    }) in
                               (match uu____17483 with
                                | Failed uu____17492 -> fallback ()
                                | Success uu____17497 ->
                                    let guard =
                                      let uu____17501 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____17506 =
                                        let uu____17507 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____17507
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____17501
                                        uu____17506 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___282_17516 = wl1 in
                                      {
                                        attempting =
                                          (uu___282_17516.attempting);
                                        wl_deferred =
                                          (uu___282_17516.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___282_17516.defer_ok);
                                        smt_ok = (uu___282_17516.smt_ok);
                                        tcenv = (uu___282_17516.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17518,FStar_Syntax_Syntax.Tm_uvar uu____17519) ->
                   let uu____17552 = destruct_flex_t t1 in
                   let uu____17553 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17552 uu____17553
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17554;
                     FStar_Syntax_Syntax.pos = uu____17555;
                     FStar_Syntax_Syntax.vars = uu____17556;_},uu____17557),FStar_Syntax_Syntax.Tm_uvar
                  uu____17558) ->
                   let uu____17611 = destruct_flex_t t1 in
                   let uu____17612 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17611 uu____17612
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17613,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17614;
                     FStar_Syntax_Syntax.pos = uu____17615;
                     FStar_Syntax_Syntax.vars = uu____17616;_},uu____17617))
                   ->
                   let uu____17670 = destruct_flex_t t1 in
                   let uu____17671 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17670 uu____17671
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17672;
                     FStar_Syntax_Syntax.pos = uu____17673;
                     FStar_Syntax_Syntax.vars = uu____17674;_},uu____17675),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17676;
                     FStar_Syntax_Syntax.pos = uu____17677;
                     FStar_Syntax_Syntax.vars = uu____17678;_},uu____17679))
                   ->
                   let uu____17752 = destruct_flex_t t1 in
                   let uu____17753 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17752 uu____17753
               | (FStar_Syntax_Syntax.Tm_uvar uu____17754,uu____17755) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____17772 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____17772 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17779;
                     FStar_Syntax_Syntax.pos = uu____17780;
                     FStar_Syntax_Syntax.vars = uu____17781;_},uu____17782),uu____17783)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____17820 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____17820 t2 wl
               | (uu____17827,FStar_Syntax_Syntax.Tm_uvar uu____17828) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____17845,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17846;
                     FStar_Syntax_Syntax.pos = uu____17847;
                     FStar_Syntax_Syntax.vars = uu____17848;_},uu____17849))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17886,FStar_Syntax_Syntax.Tm_type uu____17887) ->
                   solve_t' env
                     (let uu___283_17905 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___283_17905.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___283_17905.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___283_17905.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___283_17905.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___283_17905.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___283_17905.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___283_17905.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___283_17905.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___283_17905.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17906;
                     FStar_Syntax_Syntax.pos = uu____17907;
                     FStar_Syntax_Syntax.vars = uu____17908;_},uu____17909),FStar_Syntax_Syntax.Tm_type
                  uu____17910) ->
                   solve_t' env
                     (let uu___283_17948 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___283_17948.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___283_17948.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___283_17948.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___283_17948.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___283_17948.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___283_17948.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___283_17948.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___283_17948.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___283_17948.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17949,FStar_Syntax_Syntax.Tm_arrow uu____17950) ->
                   solve_t' env
                     (let uu___283_17980 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___283_17980.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___283_17980.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___283_17980.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___283_17980.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___283_17980.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___283_17980.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___283_17980.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___283_17980.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___283_17980.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17981;
                     FStar_Syntax_Syntax.pos = uu____17982;
                     FStar_Syntax_Syntax.vars = uu____17983;_},uu____17984),FStar_Syntax_Syntax.Tm_arrow
                  uu____17985) ->
                   solve_t' env
                     (let uu___283_18035 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___283_18035.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___283_18035.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___283_18035.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___283_18035.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___283_18035.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___283_18035.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___283_18035.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___283_18035.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___283_18035.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18036,uu____18037) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18056 =
                        let uu____18057 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18057 in
                      if uu____18056
                      then
                        let uu____18058 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___284_18064 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___284_18064.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___284_18064.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___284_18064.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___284_18064.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___284_18064.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___284_18064.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___284_18064.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___284_18064.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___284_18064.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18065 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18058 uu____18065 t2
                          wl
                      else
                        (let uu____18073 = base_and_refinement env t2 in
                         match uu____18073 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18102 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___285_18108 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___285_18108.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___285_18108.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___285_18108.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___285_18108.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___285_18108.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___285_18108.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___285_18108.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___285_18108.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___285_18108.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18109 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18102
                                    uu____18109 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___286_18123 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___286_18123.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___286_18123.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18126 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_72  ->
                                         FStar_TypeChecker_Common.TProb _0_72)
                                      uu____18126 in
                                  let guard =
                                    let uu____18138 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18138
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18146;
                     FStar_Syntax_Syntax.pos = uu____18147;
                     FStar_Syntax_Syntax.vars = uu____18148;_},uu____18149),uu____18150)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18189 =
                        let uu____18190 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18190 in
                      if uu____18189
                      then
                        let uu____18191 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___284_18197 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___284_18197.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___284_18197.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___284_18197.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___284_18197.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___284_18197.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___284_18197.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___284_18197.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___284_18197.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___284_18197.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18198 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18191 uu____18198 t2
                          wl
                      else
                        (let uu____18206 = base_and_refinement env t2 in
                         match uu____18206 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18235 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___285_18241 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___285_18241.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___285_18241.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___285_18241.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___285_18241.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___285_18241.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___285_18241.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___285_18241.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___285_18241.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___285_18241.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18242 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18235
                                    uu____18242 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___286_18256 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___286_18256.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___286_18256.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18259 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_75  ->
                                         FStar_TypeChecker_Common.TProb _0_75)
                                      uu____18259 in
                                  let guard =
                                    let uu____18271 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18271
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18279,FStar_Syntax_Syntax.Tm_uvar uu____18280) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18298 = base_and_refinement env t1 in
                      match uu____18298 with
                      | (t_base,uu____18310) ->
                          solve_t env
                            (let uu___287_18324 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___287_18324.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___287_18324.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___287_18324.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___287_18324.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___287_18324.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___287_18324.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___287_18324.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___287_18324.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18325,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18326;
                     FStar_Syntax_Syntax.pos = uu____18327;
                     FStar_Syntax_Syntax.vars = uu____18328;_},uu____18329))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18367 = base_and_refinement env t1 in
                      match uu____18367 with
                      | (t_base,uu____18379) ->
                          solve_t env
                            (let uu___287_18393 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___287_18393.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___287_18393.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___287_18393.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___287_18393.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___287_18393.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___287_18393.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___287_18393.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___287_18393.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____18394,uu____18395) ->
                   let t21 =
                     let uu____18405 = base_and_refinement env t2 in
                     FStar_All.pipe_left force_refinement uu____18405 in
                   solve_t env
                     (let uu___288_18429 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___288_18429.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___288_18429.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___288_18429.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___288_18429.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___288_18429.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___288_18429.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___288_18429.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___288_18429.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___288_18429.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____18430,FStar_Syntax_Syntax.Tm_refine uu____18431) ->
                   let t11 =
                     let uu____18441 = base_and_refinement env t1 in
                     FStar_All.pipe_left force_refinement uu____18441 in
                   solve_t env
                     (let uu___289_18465 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___289_18465.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___289_18465.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___289_18465.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___289_18465.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___289_18465.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___289_18465.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___289_18465.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___289_18465.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___289_18465.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____18468,uu____18469) ->
                   let head1 =
                     let uu____18495 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18495
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18539 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18539
                       FStar_Pervasives_Native.fst in
                   let uu____18580 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18580
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18595 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18595
                      then
                        let guard =
                          let uu____18607 =
                            let uu____18608 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18608 = FStar_Syntax_Util.Equal in
                          if uu____18607
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18612 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____18612) in
                        let uu____18615 = solve_prob orig guard [] wl in
                        solve env uu____18615
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____18618,uu____18619) ->
                   let head1 =
                     let uu____18629 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18629
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18673 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18673
                       FStar_Pervasives_Native.fst in
                   let uu____18714 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18714
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18729 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18729
                      then
                        let guard =
                          let uu____18741 =
                            let uu____18742 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18742 = FStar_Syntax_Util.Equal in
                          if uu____18741
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18746 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____18746) in
                        let uu____18749 = solve_prob orig guard [] wl in
                        solve env uu____18749
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____18752,uu____18753) ->
                   let head1 =
                     let uu____18757 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18757
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18801 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18801
                       FStar_Pervasives_Native.fst in
                   let uu____18842 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18842
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18857 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18857
                      then
                        let guard =
                          let uu____18869 =
                            let uu____18870 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18870 = FStar_Syntax_Util.Equal in
                          if uu____18869
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18874 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____18874) in
                        let uu____18877 = solve_prob orig guard [] wl in
                        solve env uu____18877
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____18880,uu____18881) ->
                   let head1 =
                     let uu____18885 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18885
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18929 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18929
                       FStar_Pervasives_Native.fst in
                   let uu____18970 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18970
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18985 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18985
                      then
                        let guard =
                          let uu____18997 =
                            let uu____18998 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18998 = FStar_Syntax_Util.Equal in
                          if uu____18997
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19002 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____19002) in
                        let uu____19005 = solve_prob orig guard [] wl in
                        solve env uu____19005
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____19008,uu____19009) ->
                   let head1 =
                     let uu____19013 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19013
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19057 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19057
                       FStar_Pervasives_Native.fst in
                   let uu____19098 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19098
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19113 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19113
                      then
                        let guard =
                          let uu____19125 =
                            let uu____19126 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19126 = FStar_Syntax_Util.Equal in
                          if uu____19125
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19130 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19130) in
                        let uu____19133 = solve_prob orig guard [] wl in
                        solve env uu____19133
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19136,uu____19137) ->
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
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19272) in
                        let uu____19275 = solve_prob orig guard [] wl in
                        solve env uu____19275
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19278,FStar_Syntax_Syntax.Tm_match uu____19279) ->
                   let head1 =
                     let uu____19305 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19305
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19349 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19349
                       FStar_Pervasives_Native.fst in
                   let uu____19390 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19390
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19405 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19405
                      then
                        let guard =
                          let uu____19417 =
                            let uu____19418 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19418 = FStar_Syntax_Util.Equal in
                          if uu____19417
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19422 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____19422) in
                        let uu____19425 = solve_prob orig guard [] wl in
                        solve env uu____19425
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19428,FStar_Syntax_Syntax.Tm_uinst uu____19429) ->
                   let head1 =
                     let uu____19439 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19439
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19483 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19483
                       FStar_Pervasives_Native.fst in
                   let uu____19524 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19524
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19539 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19539
                      then
                        let guard =
                          let uu____19551 =
                            let uu____19552 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19552 = FStar_Syntax_Util.Equal in
                          if uu____19551
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19556 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____19556) in
                        let uu____19559 = solve_prob orig guard [] wl in
                        solve env uu____19559
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19562,FStar_Syntax_Syntax.Tm_name uu____19563) ->
                   let head1 =
                     let uu____19567 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19567
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19611 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19611
                       FStar_Pervasives_Native.fst in
                   let uu____19652 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19652
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19667 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19667
                      then
                        let guard =
                          let uu____19679 =
                            let uu____19680 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19680 = FStar_Syntax_Util.Equal in
                          if uu____19679
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19684 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____19684) in
                        let uu____19687 = solve_prob orig guard [] wl in
                        solve env uu____19687
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19690,FStar_Syntax_Syntax.Tm_constant uu____19691) ->
                   let head1 =
                     let uu____19695 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19695
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19739 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19739
                       FStar_Pervasives_Native.fst in
                   let uu____19780 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19780
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19795 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19795
                      then
                        let guard =
                          let uu____19807 =
                            let uu____19808 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19808 = FStar_Syntax_Util.Equal in
                          if uu____19807
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19812 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____19812) in
                        let uu____19815 = solve_prob orig guard [] wl in
                        solve env uu____19815
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19818,FStar_Syntax_Syntax.Tm_fvar uu____19819) ->
                   let head1 =
                     let uu____19823 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19823
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19867 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19867
                       FStar_Pervasives_Native.fst in
                   let uu____19908 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19908
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19923 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19923
                      then
                        let guard =
                          let uu____19935 =
                            let uu____19936 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19936 = FStar_Syntax_Util.Equal in
                          if uu____19935
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19940 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____19940) in
                        let uu____19943 = solve_prob orig guard [] wl in
                        solve env uu____19943
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19946,FStar_Syntax_Syntax.Tm_app uu____19947) ->
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
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____20082) in
                        let uu____20085 = solve_prob orig guard [] wl in
                        solve env uu____20085
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let uu____20088,uu____20089) ->
                   let uu____20102 =
                     let uu____20103 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20104 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20103
                       uu____20104 in
                   failwith uu____20102
               | (FStar_Syntax_Syntax.Tm_delayed uu____20105,uu____20106) ->
                   let uu____20131 =
                     let uu____20132 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20133 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20132
                       uu____20133 in
                   failwith uu____20131
               | (uu____20134,FStar_Syntax_Syntax.Tm_delayed uu____20135) ->
                   let uu____20160 =
                     let uu____20161 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20162 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20161
                       uu____20162 in
                   failwith uu____20160
               | (uu____20163,FStar_Syntax_Syntax.Tm_let uu____20164) ->
                   let uu____20177 =
                     let uu____20178 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20179 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20178
                       uu____20179 in
                   failwith uu____20177
               | uu____20180 -> giveup env "head tag mismatch" orig)))
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
          (let uu____20216 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____20216
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____20218 =
               let uu____20219 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name in
               let uu____20220 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20219 uu____20220 in
             giveup env uu____20218 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____20240  ->
                    fun uu____20241  ->
                      match (uu____20240, uu____20241) with
                      | ((a1,uu____20259),(a2,uu____20261)) ->
                          let uu____20270 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg" in
                          FStar_All.pipe_left
                            (fun _0_88  ->
                               FStar_TypeChecker_Common.TProb _0_88)
                            uu____20270)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args in
             let guard =
               let uu____20280 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs in
               FStar_Syntax_Util.mk_conj_l uu____20280 in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
             solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____20304 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20311)::[] -> wp1
              | uu____20328 ->
                  let uu____20337 =
                    let uu____20338 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20338 in
                  failwith uu____20337 in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____20346 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ in
                  [uu____20346]
              | x -> x in
            let uu____20348 =
              let uu____20357 =
                let uu____20358 =
                  let uu____20359 = FStar_List.hd univs1 in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____20359 c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____20358 in
              [uu____20357] in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20348;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20360 = lift_c1 () in solve_eq uu____20360 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___243_20366  ->
                       match uu___243_20366 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20367 -> false)) in
             let uu____20368 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20402)::uu____20403,(wp2,uu____20405)::uu____20406)
                   -> (wp1, wp2)
               | uu____20463 ->
                   let uu____20484 =
                     let uu____20485 =
                       let uu____20490 =
                         let uu____20491 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____20492 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____20491 uu____20492 in
                       (uu____20490, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____20485 in
                   FStar_Exn.raise uu____20484 in
             match uu____20368 with
             | (wpc1,wpc2) ->
                 let uu____20511 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____20511
                 then
                   let uu____20514 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____20514 wl
                 else
                   (let uu____20518 =
                      let uu____20525 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____20525 in
                    match uu____20518 with
                    | (c2_decl,qualifiers) ->
                        let uu____20546 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____20546
                        then
                          let c1_repr =
                            let uu____20550 =
                              let uu____20551 =
                                let uu____20552 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____20552 in
                              let uu____20553 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20551 uu____20553 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20550 in
                          let c2_repr =
                            let uu____20555 =
                              let uu____20556 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____20557 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20556 uu____20557 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20555 in
                          let prob =
                            let uu____20559 =
                              let uu____20564 =
                                let uu____20565 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____20566 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____20565
                                  uu____20566 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____20564 in
                            FStar_TypeChecker_Common.TProb uu____20559 in
                          let wl1 =
                            let uu____20568 =
                              let uu____20571 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____20571 in
                            solve_prob orig uu____20568 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____20580 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____20580
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ in
                                   let uu____20583 =
                                     let uu____20586 =
                                       let uu____20587 =
                                         let uu____20602 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____20603 =
                                           let uu____20606 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____20607 =
                                             let uu____20610 =
                                               let uu____20611 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20611 in
                                             [uu____20610] in
                                           uu____20606 :: uu____20607 in
                                         (uu____20602, uu____20603) in
                                       FStar_Syntax_Syntax.Tm_app uu____20587 in
                                     FStar_Syntax_Syntax.mk uu____20586 in
                                   uu____20583 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ in
                                  let uu____20620 =
                                    let uu____20623 =
                                      let uu____20624 =
                                        let uu____20639 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____20640 =
                                          let uu____20643 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____20644 =
                                            let uu____20647 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____20648 =
                                              let uu____20651 =
                                                let uu____20652 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20652 in
                                              [uu____20651] in
                                            uu____20647 :: uu____20648 in
                                          uu____20643 :: uu____20644 in
                                        (uu____20639, uu____20640) in
                                      FStar_Syntax_Syntax.Tm_app uu____20624 in
                                    FStar_Syntax_Syntax.mk uu____20623 in
                                  uu____20620 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____20659 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____20659 in
                           let wl1 =
                             let uu____20669 =
                               let uu____20672 =
                                 let uu____20675 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____20675 g in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____20672 in
                             solve_prob orig uu____20669 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____20688 = FStar_Util.physical_equality c1 c2 in
        if uu____20688
        then
          let uu____20689 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____20689
        else
          ((let uu____20692 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____20692
            then
              let uu____20693 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____20694 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____20693
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____20694
            else ());
           (let uu____20696 =
              let uu____20701 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____20702 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____20701, uu____20702) in
            match uu____20696 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20706),FStar_Syntax_Syntax.Total
                    (t2,uu____20708)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____20725 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20725 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20728,FStar_Syntax_Syntax.Total uu____20729) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20747),FStar_Syntax_Syntax.Total
                    (t2,uu____20749)) ->
                     let uu____20766 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20766 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20770),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20772)) ->
                     let uu____20789 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20789 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20793),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20795)) ->
                     let uu____20812 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20812 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20815,FStar_Syntax_Syntax.Comp uu____20816) ->
                     let uu____20825 =
                       let uu___290_20830 = problem in
                       let uu____20835 =
                         let uu____20836 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20836 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___290_20830.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20835;
                         FStar_TypeChecker_Common.relation =
                           (uu___290_20830.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___290_20830.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___290_20830.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___290_20830.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___290_20830.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___290_20830.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___290_20830.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___290_20830.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20825 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____20837,FStar_Syntax_Syntax.Comp uu____20838) ->
                     let uu____20847 =
                       let uu___290_20852 = problem in
                       let uu____20857 =
                         let uu____20858 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20858 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___290_20852.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20857;
                         FStar_TypeChecker_Common.relation =
                           (uu___290_20852.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___290_20852.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___290_20852.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___290_20852.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___290_20852.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___290_20852.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___290_20852.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___290_20852.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20847 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20859,FStar_Syntax_Syntax.GTotal uu____20860) ->
                     let uu____20869 =
                       let uu___291_20874 = problem in
                       let uu____20879 =
                         let uu____20880 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20880 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___291_20874.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___291_20874.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___291_20874.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20879;
                         FStar_TypeChecker_Common.element =
                           (uu___291_20874.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___291_20874.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___291_20874.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___291_20874.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___291_20874.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___291_20874.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20869 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20881,FStar_Syntax_Syntax.Total uu____20882) ->
                     let uu____20891 =
                       let uu___291_20896 = problem in
                       let uu____20901 =
                         let uu____20902 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20902 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___291_20896.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___291_20896.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___291_20896.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20901;
                         FStar_TypeChecker_Common.element =
                           (uu___291_20896.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___291_20896.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___291_20896.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___291_20896.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___291_20896.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___291_20896.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20891 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20903,FStar_Syntax_Syntax.Comp uu____20904) ->
                     let uu____20905 =
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
                     if uu____20905
                     then
                       let uu____20906 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____20906 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____20912 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____20922 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____20923 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____20922, uu____20923)) in
                          match uu____20912 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu____20930 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____20930
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____20932 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____20932 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____20935 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____20937 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____20937) in
                                if uu____20935
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
                                  (let uu____20940 =
                                     let uu____20941 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____20942 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____20941 uu____20942 in
                                   giveup env uu____20940 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____20947 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____20985  ->
              match uu____20985 with
              | (uu____20998,uu____20999,u,uu____21001,uu____21002,uu____21003)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____20947 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____21034 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____21034 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____21052 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21080  ->
                match uu____21080 with
                | (u1,u2) ->
                    let uu____21087 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____21088 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____21087 uu____21088)) in
      FStar_All.pipe_right uu____21052 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21105,[])) -> "{}"
      | uu____21130 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21147 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____21147
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____21150 =
              FStar_List.map
                (fun uu____21160  ->
                   match uu____21160 with
                   | (uu____21165,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____21150 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____21170 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21170 imps
let new_t_problem:
  'Auu____21178 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21178 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21178)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21212 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel") in
                if uu____21212
                then
                  let uu____21213 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs in
                  let uu____21214 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21213
                    (rel_to_string rel) uu____21214
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
            let uu____21238 =
              let uu____21241 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____21241 in
            FStar_Syntax_Syntax.new_bv uu____21238 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____21250 =
              let uu____21253 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____21253 in
            let uu____21256 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____21250 uu____21256 in
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
          let uu____21286 = FStar_Options.eager_inference () in
          if uu____21286
          then
            let uu___292_21287 = probs in
            {
              attempting = (uu___292_21287.attempting);
              wl_deferred = (uu___292_21287.wl_deferred);
              ctr = (uu___292_21287.ctr);
              defer_ok = false;
              smt_ok = (uu___292_21287.smt_ok);
              tcenv = (uu___292_21287.tcenv)
            }
          else probs in
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        let sol = solve env probs1 in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            ((let uu____21298 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____21298
              then
                let uu____21299 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____21299
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
          ((let uu____21313 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____21313
            then
              let uu____21314 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21314
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f in
            (let uu____21318 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____21318
             then
               let uu____21319 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21319
             else ());
            (let f2 =
               let uu____21322 =
                 let uu____21323 = FStar_Syntax_Util.unmeta f1 in
                 uu____21323.FStar_Syntax_Syntax.n in
               match uu____21322 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21327 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___293_21328 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___293_21328.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___293_21328.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___293_21328.FStar_TypeChecker_Env.implicits)
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
            let uu____21347 =
              let uu____21348 =
                let uu____21349 =
                  let uu____21350 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____21350
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21349;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____21348 in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____21347
let with_guard_no_simp:
  'Auu____21377 .
    'Auu____21377 ->
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
            let uu____21397 =
              let uu____21398 =
                let uu____21399 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____21399
                  (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
              {
                FStar_TypeChecker_Env.guard_f = uu____21398;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              } in
            FStar_Pervasives_Native.Some uu____21397
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
          (let uu____21437 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21437
           then
             let uu____21438 = FStar_Syntax_Print.term_to_string t1 in
             let uu____21439 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21438
               uu____21439
           else ());
          (let prob =
             let uu____21442 =
               let uu____21447 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____21447 in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____21442 in
           let g =
             let uu____21455 =
               let uu____21458 = singleton' env prob smt_ok in
               solve_and_commit env uu____21458
                 (fun uu____21460  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____21455 in
           g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21478 = try_teq true env t1 t2 in
        match uu____21478 with
        | FStar_Pervasives_Native.None  ->
            let uu____21481 =
              let uu____21482 =
                let uu____21487 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____21488 = FStar_TypeChecker_Env.get_range env in
                (uu____21487, uu____21488) in
              FStar_Errors.Error uu____21482 in
            FStar_Exn.raise uu____21481
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21491 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____21491
              then
                let uu____21492 = FStar_Syntax_Print.term_to_string t1 in
                let uu____21493 = FStar_Syntax_Print.term_to_string t2 in
                let uu____21494 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21492
                  uu____21493 uu____21494
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
          let uu____21508 = FStar_TypeChecker_Env.get_range env in
          let uu____21509 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____21508 uu____21509
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____21522 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____21522
         then
           let uu____21523 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____21524 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____21523
             uu____21524
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____21529 =
             let uu____21534 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____21534 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____21529 in
         let uu____21539 =
           let uu____21542 = singleton env prob in
           solve_and_commit env uu____21542
             (fun uu____21544  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____21539)
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
      fun uu____21573  ->
        match uu____21573 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____21612 =
                 let uu____21613 =
                   let uu____21618 =
                     let uu____21619 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____21620 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____21619 uu____21620 in
                   let uu____21621 = FStar_TypeChecker_Env.get_range env in
                   (uu____21618, uu____21621) in
                 FStar_Errors.Error uu____21613 in
               FStar_Exn.raise uu____21612) in
            let equiv1 v1 v' =
              let uu____21629 =
                let uu____21634 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____21635 = FStar_Syntax_Subst.compress_univ v' in
                (uu____21634, uu____21635) in
              match uu____21629 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____21654 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____21684 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____21684 with
                      | FStar_Syntax_Syntax.U_unif uu____21691 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____21720  ->
                                    match uu____21720 with
                                    | (u,v') ->
                                        let uu____21729 = equiv1 v1 v' in
                                        if uu____21729
                                        then
                                          let uu____21732 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____21732 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____21748 -> [])) in
            let uu____21753 =
              let wl =
                let uu___294_21757 = empty_worklist env in
                {
                  attempting = (uu___294_21757.attempting);
                  wl_deferred = (uu___294_21757.wl_deferred);
                  ctr = (uu___294_21757.ctr);
                  defer_ok = false;
                  smt_ok = (uu___294_21757.smt_ok);
                  tcenv = (uu___294_21757.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____21775  ->
                      match uu____21775 with
                      | (lb,v1) ->
                          let uu____21782 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____21782 with
                           | USolved wl1 -> ()
                           | uu____21784 -> fail lb v1))) in
            let rec check_ineq uu____21792 =
              match uu____21792 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____21801) -> true
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
                      uu____21824,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____21826,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____21837) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____21844,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____21852 -> false) in
            let uu____21857 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____21872  ->
                      match uu____21872 with
                      | (u,v1) ->
                          let uu____21879 = check_ineq (u, v1) in
                          if uu____21879
                          then true
                          else
                            ((let uu____21882 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____21882
                              then
                                let uu____21883 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____21884 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____21883
                                  uu____21884
                              else ());
                             false))) in
            if uu____21857
            then ()
            else
              ((let uu____21888 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____21888
                then
                  ((let uu____21890 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____21890);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____21900 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____21900))
                else ());
               (let uu____21910 =
                  let uu____21911 =
                    let uu____21916 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____21916) in
                  FStar_Errors.Error uu____21911 in
                FStar_Exn.raise uu____21910))
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
      let fail uu____21964 =
        match uu____21964 with
        | (d,s) ->
            let msg = explain env d s in
            FStar_Exn.raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____21978 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____21978
       then
         let uu____21979 = wl_to_string wl in
         let uu____21980 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____21979 uu____21980
       else ());
      (let g1 =
         let uu____21995 = solve_and_commit env wl fail in
         match uu____21995 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___295_22008 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___295_22008.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___295_22008.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___295_22008.FStar_TypeChecker_Env.implicits)
             }
         | uu____22013 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___296_22017 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___296_22017.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___296_22017.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___296_22017.FStar_TypeChecker_Env.implicits)
        }))
let last_proof_ns:
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let maybe_update_proof_ns: FStar_TypeChecker_Env.env -> Prims.unit =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____22039 = FStar_ST.op_Bang last_proof_ns in
    match uu____22039 with
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
            let uu___297_22223 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___297_22223.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___297_22223.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___297_22223.FStar_TypeChecker_Env.implicits)
            } in
          let uu____22224 =
            let uu____22225 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____22225 in
          if uu____22224
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22233 = FStar_TypeChecker_Env.get_range env in
                     let uu____22234 =
                       let uu____22235 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22235 in
                     FStar_Errors.diag uu____22233 uu____22234)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   if debug1
                   then
                     (let uu____22239 = FStar_TypeChecker_Env.get_range env in
                      let uu____22240 =
                        let uu____22241 =
                          FStar_Syntax_Print.term_to_string vc1 in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22241 in
                      FStar_Errors.diag uu____22239 uu____22240)
                   else ();
                   (let uu____22243 = check_trivial vc1 in
                    match uu____22243 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22250 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22251 =
                                let uu____22252 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22252 in
                              FStar_Errors.diag uu____22250 uu____22251)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22257 =
                                FStar_TypeChecker_Env.get_range env in
                              let uu____22258 =
                                let uu____22259 =
                                  FStar_Syntax_Print.term_to_string vc2 in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22259 in
                              FStar_Errors.diag uu____22257 uu____22258)
                           else ();
                           (let vcs =
                              let uu____22270 = FStar_Options.use_tactics () in
                              if uu____22270
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22289  ->
                                     (let uu____22291 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics" in
                                      FStar_All.pipe_left
                                        FStar_Pervasives.ignore uu____22291);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____22293 =
                                   let uu____22300 = FStar_Options.peek () in
                                   (env, vc2, uu____22300) in
                                 [uu____22293]) in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22334  ->
                                    match uu____22334 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal in
                                        let uu____22345 = check_trivial goal1 in
                                        (match uu____22345 with
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
                                                (let uu____22353 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22354 =
                                                   let uu____22355 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   let uu____22356 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1 in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22355 uu____22356 in
                                                 FStar_Errors.diag
                                                   uu____22353 uu____22354)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22359 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1 in
                                                 let uu____22360 =
                                                   let uu____22361 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2 in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22361 in
                                                 FStar_Errors.diag
                                                   uu____22359 uu____22360)
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
      let uu____22371 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____22371 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22377 =
            let uu____22378 =
              let uu____22383 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____22383) in
            FStar_Errors.Error uu____22378 in
          FStar_Exn.raise uu____22377
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____22390 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____22390 with
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
          let uu____22409 = FStar_Syntax_Unionfind.find u in
          match uu____22409 with
          | FStar_Pervasives_Native.None  -> true
          | uu____22412 -> false in
        let rec until_fixpoint acc implicits =
          let uu____22430 = acc in
          match uu____22430 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____22516 = hd1 in
                   (match uu____22516 with
                    | (uu____22529,env,u,tm,k,r) ->
                        let uu____22535 = unresolved u in
                        if uu____22535
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let env1 =
                             FStar_TypeChecker_Env.set_expected_typ env k in
                           let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env1 tm in
                           (let uu____22566 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck") in
                            if uu____22566
                            then
                              let uu____22567 =
                                FStar_Syntax_Print.uvar_to_string u in
                              let uu____22568 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____22569 =
                                FStar_Syntax_Print.term_to_string k in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____22567 uu____22568 uu____22569
                            else ());
                           (let env2 =
                              if forcelax
                              then
                                let uu___298_22572 = env1 in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___298_22572.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___298_22572.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___298_22572.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___298_22572.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___298_22572.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___298_22572.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___298_22572.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___298_22572.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___298_22572.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___298_22572.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___298_22572.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___298_22572.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___298_22572.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___298_22572.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___298_22572.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___298_22572.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___298_22572.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___298_22572.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax = true;
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___298_22572.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___298_22572.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___298_22572.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___298_22572.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___298_22572.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___298_22572.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___298_22572.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___298_22572.FStar_TypeChecker_Env.qname_and_index);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___298_22572.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth =
                                    (uu___298_22572.FStar_TypeChecker_Env.synth);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___298_22572.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___298_22572.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___298_22572.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___298_22572.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.dep_graph =
                                    (uu___298_22572.FStar_TypeChecker_Env.dep_graph)
                                }
                              else env1 in
                            let g1 =
                              if must_total
                              then
                                let uu____22575 =
                                  env2.FStar_TypeChecker_Env.type_of
                                    (let uu___299_22583 = env2 in
                                     {
                                       FStar_TypeChecker_Env.solver =
                                         (uu___299_22583.FStar_TypeChecker_Env.solver);
                                       FStar_TypeChecker_Env.range =
                                         (uu___299_22583.FStar_TypeChecker_Env.range);
                                       FStar_TypeChecker_Env.curmodule =
                                         (uu___299_22583.FStar_TypeChecker_Env.curmodule);
                                       FStar_TypeChecker_Env.gamma =
                                         (uu___299_22583.FStar_TypeChecker_Env.gamma);
                                       FStar_TypeChecker_Env.gamma_cache =
                                         (uu___299_22583.FStar_TypeChecker_Env.gamma_cache);
                                       FStar_TypeChecker_Env.modules =
                                         (uu___299_22583.FStar_TypeChecker_Env.modules);
                                       FStar_TypeChecker_Env.expected_typ =
                                         (uu___299_22583.FStar_TypeChecker_Env.expected_typ);
                                       FStar_TypeChecker_Env.sigtab =
                                         (uu___299_22583.FStar_TypeChecker_Env.sigtab);
                                       FStar_TypeChecker_Env.is_pattern =
                                         (uu___299_22583.FStar_TypeChecker_Env.is_pattern);
                                       FStar_TypeChecker_Env.instantiate_imp
                                         =
                                         (uu___299_22583.FStar_TypeChecker_Env.instantiate_imp);
                                       FStar_TypeChecker_Env.effects =
                                         (uu___299_22583.FStar_TypeChecker_Env.effects);
                                       FStar_TypeChecker_Env.generalize =
                                         (uu___299_22583.FStar_TypeChecker_Env.generalize);
                                       FStar_TypeChecker_Env.letrecs =
                                         (uu___299_22583.FStar_TypeChecker_Env.letrecs);
                                       FStar_TypeChecker_Env.top_level =
                                         (uu___299_22583.FStar_TypeChecker_Env.top_level);
                                       FStar_TypeChecker_Env.check_uvars =
                                         (uu___299_22583.FStar_TypeChecker_Env.check_uvars);
                                       FStar_TypeChecker_Env.use_eq =
                                         (uu___299_22583.FStar_TypeChecker_Env.use_eq);
                                       FStar_TypeChecker_Env.is_iface =
                                         (uu___299_22583.FStar_TypeChecker_Env.is_iface);
                                       FStar_TypeChecker_Env.admit =
                                         (uu___299_22583.FStar_TypeChecker_Env.admit);
                                       FStar_TypeChecker_Env.lax =
                                         (uu___299_22583.FStar_TypeChecker_Env.lax);
                                       FStar_TypeChecker_Env.lax_universes =
                                         (uu___299_22583.FStar_TypeChecker_Env.lax_universes);
                                       FStar_TypeChecker_Env.failhard =
                                         (uu___299_22583.FStar_TypeChecker_Env.failhard);
                                       FStar_TypeChecker_Env.nosynth =
                                         (uu___299_22583.FStar_TypeChecker_Env.nosynth);
                                       FStar_TypeChecker_Env.tc_term =
                                         (uu___299_22583.FStar_TypeChecker_Env.tc_term);
                                       FStar_TypeChecker_Env.type_of =
                                         (uu___299_22583.FStar_TypeChecker_Env.type_of);
                                       FStar_TypeChecker_Env.universe_of =
                                         (uu___299_22583.FStar_TypeChecker_Env.universe_of);
                                       FStar_TypeChecker_Env.use_bv_sorts =
                                         true;
                                       FStar_TypeChecker_Env.qname_and_index
                                         =
                                         (uu___299_22583.FStar_TypeChecker_Env.qname_and_index);
                                       FStar_TypeChecker_Env.proof_ns =
                                         (uu___299_22583.FStar_TypeChecker_Env.proof_ns);
                                       FStar_TypeChecker_Env.synth =
                                         (uu___299_22583.FStar_TypeChecker_Env.synth);
                                       FStar_TypeChecker_Env.is_native_tactic
                                         =
                                         (uu___299_22583.FStar_TypeChecker_Env.is_native_tactic);
                                       FStar_TypeChecker_Env.identifier_info
                                         =
                                         (uu___299_22583.FStar_TypeChecker_Env.identifier_info);
                                       FStar_TypeChecker_Env.tc_hooks =
                                         (uu___299_22583.FStar_TypeChecker_Env.tc_hooks);
                                       FStar_TypeChecker_Env.dsenv =
                                         (uu___299_22583.FStar_TypeChecker_Env.dsenv);
                                       FStar_TypeChecker_Env.dep_graph =
                                         (uu___299_22583.FStar_TypeChecker_Env.dep_graph)
                                     }) tm1 in
                                match uu____22575 with
                                | (uu____22584,uu____22585,g1) -> g1
                              else
                                (let uu____22588 =
                                   env2.FStar_TypeChecker_Env.tc_term
                                     (let uu___300_22596 = env2 in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___300_22596.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___300_22596.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___300_22596.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___300_22596.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___300_22596.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___300_22596.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___300_22596.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___300_22596.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___300_22596.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___300_22596.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___300_22596.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___300_22596.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___300_22596.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___300_22596.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___300_22596.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___300_22596.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___300_22596.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___300_22596.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___300_22596.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___300_22596.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___300_22596.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___300_22596.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___300_22596.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___300_22596.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___300_22596.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          true;
                                        FStar_TypeChecker_Env.qname_and_index
                                          =
                                          (uu___300_22596.FStar_TypeChecker_Env.qname_and_index);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___300_22596.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth =
                                          (uu___300_22596.FStar_TypeChecker_Env.synth);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___300_22596.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___300_22596.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___300_22596.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___300_22596.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___300_22596.FStar_TypeChecker_Env.dep_graph)
                                      }) tm1 in
                                 match uu____22588 with
                                 | (uu____22597,uu____22598,g1) -> g1) in
                            let g2 =
                              if env2.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___301_22601 = g1 in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___301_22601.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___301_22601.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___301_22601.FStar_TypeChecker_Env.implicits)
                                }
                              else g1 in
                            let g' =
                              let uu____22604 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____22610  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env2 g2 true in
                              match uu____22604 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1)))) in
        let uu___302_22638 = g in
        let uu____22639 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___302_22638.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___302_22638.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___302_22638.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____22639
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
        let uu____22693 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____22693 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____22706 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____22706
      | (reason,uu____22708,uu____22709,e,t,r)::uu____22713 ->
          let uu____22740 =
            let uu____22741 =
              let uu____22746 =
                let uu____22747 = FStar_Syntax_Print.term_to_string t in
                let uu____22748 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format2
                  "Failed to resolve implicit argument of type '%s' introduced in %s"
                  uu____22747 uu____22748 in
              (uu____22746, r) in
            FStar_Errors.Error uu____22741 in
          FStar_Exn.raise uu____22740
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___303_22755 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___303_22755.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___303_22755.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___303_22755.FStar_TypeChecker_Env.implicits)
      }
let discharge_guard_nosmt:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool =
  fun env  ->
    fun g  ->
      let uu____22778 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____22778 with
      | FStar_Pervasives_Native.Some uu____22783 -> true
      | FStar_Pervasives_Native.None  -> false
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22793 = try_teq false env t1 t2 in
        match uu____22793 with
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
        (let uu____22813 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____22813
         then
           let uu____22814 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____22815 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____22814
             uu____22815
         else ());
        (let uu____22817 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
         match uu____22817 with
         | (prob,x) ->
             let g =
               let uu____22833 =
                 let uu____22836 = singleton' env prob true in
                 solve_and_commit env uu____22836
                   (fun uu____22838  -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____22833 in
             ((let uu____22848 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g) in
               if uu____22848
               then
                 let uu____22849 =
                   FStar_TypeChecker_Normalize.term_to_string env t1 in
                 let uu____22850 =
                   FStar_TypeChecker_Normalize.term_to_string env t2 in
                 let uu____22851 =
                   let uu____22852 = FStar_Util.must g in
                   guard_to_string env uu____22852 in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____22849 uu____22850 uu____22851
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
        let uu____22880 = check_subtyping env t1 t2 in
        match uu____22880 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____22899 =
              let uu____22900 = FStar_Syntax_Syntax.mk_binder x in
              abstract_guard uu____22900 g in
            FStar_Pervasives_Native.Some uu____22899
let get_subtyping_prop:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22912 = check_subtyping env t1 t2 in
        match uu____22912 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____22931 =
              let uu____22932 =
                let uu____22933 = FStar_Syntax_Syntax.mk_binder x in
                [uu____22933] in
              close_guard env uu____22932 g in
            FStar_Pervasives_Native.Some uu____22931
let subtype_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____22944 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____22944
         then
           let uu____22945 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____22946 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____22945
             uu____22946
         else ());
        (let uu____22948 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
         match uu____22948 with
         | (prob,x) ->
             let g =
               let uu____22958 =
                 let uu____22961 = singleton' env prob false in
                 solve_and_commit env uu____22961
                   (fun uu____22963  -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____22958 in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____22974 =
                      let uu____22975 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____22975] in
                    close_guard env uu____22974 g1 in
                  discharge_guard_nosmt env g2))