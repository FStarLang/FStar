open Prims
let (guard_of_guard_formula
  :FStar_TypeChecker_Common.guard_formula -> FStar_TypeChecker_Env.guard_t)=
  fun g  ->
    {
      FStar_TypeChecker_Env.guard_f = g;
      FStar_TypeChecker_Env.deferred = [];
      FStar_TypeChecker_Env.univ_ineqs = ([], []);
      FStar_TypeChecker_Env.implicits = []
    }
let (guard_form
  :FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Common.guard_formula)=
  fun g  -> g.FStar_TypeChecker_Env.guard_f
let (is_trivial :FStar_TypeChecker_Env.guard_t -> Prims.bool)=
  fun g  ->
    match g with
    | { FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Env.deferred = [];
        FStar_TypeChecker_Env.univ_ineqs = uu____33;
        FStar_TypeChecker_Env.implicits = uu____34;_} -> true
    | uu____61 -> false
let (trivial_guard :FStar_TypeChecker_Env.guard_t)=
  {
    FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial;
    FStar_TypeChecker_Env.deferred = [];
    FStar_TypeChecker_Env.univ_ineqs = ([], []);
    FStar_TypeChecker_Env.implicits = []
  }
let (abstract_guard
  :FStar_Syntax_Syntax.bv ->
     FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option ->
       FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)=
  fun x  ->
    fun g  ->
      match g with
      | FStar_Pervasives_Native.None  -> g
      | FStar_Pervasives_Native.Some
          {
            FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
            FStar_TypeChecker_Env.deferred = uu____98;
            FStar_TypeChecker_Env.univ_ineqs = uu____99;
            FStar_TypeChecker_Env.implicits = uu____100;_}
          -> g
      | FStar_Pervasives_Native.Some g1 ->
          let f =
            match g1.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.NonTrivial f -> f
            | uu____126 -> failwith "impossible" in
          let uu____127 =
            let uu___139_128 = g1 in
            let uu____129 =
              let uu____130 =
                let uu____131 =
                  let uu____132 = FStar_Syntax_Syntax.mk_binder x in
                  [uu____132] in
                FStar_Syntax_Util.abs uu____131 f
                  (FStar_Pervasives_Native.Some
                     (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0)) in
              FStar_All.pipe_left
                (fun _0_41  -> FStar_TypeChecker_Common.NonTrivial _0_41)
                uu____130 in
            {
              FStar_TypeChecker_Env.guard_f = uu____129;
              FStar_TypeChecker_Env.deferred =
                (uu___139_128.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___139_128.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___139_128.FStar_TypeChecker_Env.implicits)
            } in
          FStar_Pervasives_Native.Some uu____127
let (apply_guard
  :FStar_TypeChecker_Env.guard_t ->
     FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t)=
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___140_142 = g in
          let uu____143 =
            let uu____144 =
              let uu____145 =
                let uu____148 =
                  let uu____149 =
                    let uu____164 =
                      let uu____167 = FStar_Syntax_Syntax.as_arg e in
                      [uu____167] in
                    (f, uu____164) in
                  FStar_Syntax_Syntax.Tm_app uu____149 in
                FStar_Syntax_Syntax.mk uu____148 in
              uu____145 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun _0_42  -> FStar_TypeChecker_Common.NonTrivial _0_42)
              uu____144 in
          {
            FStar_TypeChecker_Env.guard_f = uu____143;
            FStar_TypeChecker_Env.deferred =
              (uu___140_142.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___140_142.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___140_142.FStar_TypeChecker_Env.implicits)
          }
let (map_guard
  :FStar_TypeChecker_Env.guard_t ->
     (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
       FStar_TypeChecker_Env.guard_t)=
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___141_187 = g in
          let uu____188 =
            let uu____189 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____189 in
          {
            FStar_TypeChecker_Env.guard_f = uu____188;
            FStar_TypeChecker_Env.deferred =
              (uu___141_187.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___141_187.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___141_187.FStar_TypeChecker_Env.implicits)
          }
let (trivial :FStar_TypeChecker_Common.guard_formula -> Prims.unit)=
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____194 -> failwith "impossible"
let (conj_guard_f
  :FStar_TypeChecker_Common.guard_formula ->
     FStar_TypeChecker_Common.guard_formula ->
       FStar_TypeChecker_Common.guard_formula)=
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) -> g
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let uu____207 = FStar_Syntax_Util.mk_conj f1 f2 in
          FStar_TypeChecker_Common.NonTrivial uu____207
let (check_trivial
  :FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula)=
  fun t  ->
    let uu____212 =
      let uu____213 = FStar_Syntax_Util.unmeta t in
      uu____213.FStar_Syntax_Syntax.n in
    match uu____212 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____217 -> FStar_TypeChecker_Common.NonTrivial t
let (imp_guard_f
  :FStar_TypeChecker_Common.guard_formula ->
     FStar_TypeChecker_Common.guard_formula ->
       FStar_TypeChecker_Common.guard_formula)=
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) ->
          FStar_TypeChecker_Common.Trivial
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let imp = FStar_Syntax_Util.mk_imp f1 f2 in check_trivial imp
let (binop_guard
  :(FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.guard_formula)
     ->
     FStar_TypeChecker_Env.guard_t ->
       FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)=
  fun f  ->
    fun g1  ->
      fun g2  ->
        let uu____253 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f in
        {
          FStar_TypeChecker_Env.guard_f = uu____253;
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
let (conj_guard
  :FStar_TypeChecker_Env.guard_t ->
     FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)=
  fun g1  -> fun g2  -> binop_guard conj_guard_f g1 g2
let (imp_guard
  :FStar_TypeChecker_Env.guard_t ->
     FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)=
  fun g1  -> fun g2  -> binop_guard imp_guard_f g1 g2
let (close_guard_univs
  :FStar_Syntax_Syntax.universes ->
     FStar_Syntax_Syntax.binders ->
       FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)=
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
                       let uu____327 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____327
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f in
            let uu___142_329 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___142_329.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___142_329.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___142_329.FStar_TypeChecker_Env.implicits)
            }
let (close_forall
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.binder Prims.list ->
       FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)=
  fun env  ->
    fun bs  ->
      fun f  ->
        FStar_List.fold_right
          (fun b  ->
             fun f1  ->
               let uu____351 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____351
               then f1
               else
                 (let u =
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                  FStar_Syntax_Util.mk_forall u
                    (FStar_Pervasives_Native.fst b) f1)) bs f
let (close_guard
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.binders ->
       FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)=
  fun env  ->
    fun binders  ->
      fun g  ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___143_367 = g in
            let uu____368 =
              let uu____369 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____369 in
            {
              FStar_TypeChecker_Env.guard_f = uu____368;
              FStar_TypeChecker_Env.deferred =
                (uu___143_367.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___143_367.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___143_367.FStar_TypeChecker_Env.implicits)
            }
let (new_uvar
  :FStar_Range.range ->
     FStar_Syntax_Syntax.binders ->
       FStar_Syntax_Syntax.typ ->
         (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
           FStar_Pervasives_Native.tuple2)=
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
        | uu____402 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let uu____427 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders uu____427 in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                FStar_Pervasives_Native.None r in
            let uu____435 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                FStar_Pervasives_Native.None r in
            (uu____435, uv1)
let (mk_eq2
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
       FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____466 = FStar_Syntax_Util.type_u () in
        match uu____466 with
        | (t_type,u) ->
            let uu____473 =
              let uu____478 = FStar_TypeChecker_Env.all_binders env in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____478 t_type in
            (match uu____473 with
             | (tt,uu____480) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
type uvi =
  | TERM of
  ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2
let (uu___is_TERM :uvi -> Prims.bool)=
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____514 -> false
let (__proj__TERM__item___0
  :uvi ->
     ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | TERM _0 -> _0
let (uu___is_UNIV :uvi -> Prims.bool)=
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____556 -> false
let (__proj__UNIV__item___0
  :uvi ->
     (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | UNIV _0 -> _0
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs;
  wl_deferred:
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list;
  ctr: Prims.int;
  defer_ok: Prims.bool;
  smt_ok: Prims.bool;
  tcenv: FStar_TypeChecker_Env.env;}
let (__proj__Mkworklist__item__attempting
  :worklist -> FStar_TypeChecker_Common.probs)=
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__attempting
let (__proj__Mkworklist__item__wl_deferred
  :worklist ->
     (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
       FStar_Pervasives_Native.tuple3 Prims.list)=
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__wl_deferred
let (__proj__Mkworklist__item__ctr :worklist -> Prims.int)=
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} -> __fname__ctr
let (__proj__Mkworklist__item__defer_ok :worklist -> Prims.bool)=
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__defer_ok
let (__proj__Mkworklist__item__smt_ok :worklist -> Prims.bool)=
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__smt_ok
let (__proj__Mkworklist__item__tcenv :worklist -> FStar_TypeChecker_Env.env)=
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} -> __fname__tcenv
type solution =
  | Success of FStar_TypeChecker_Common.deferred
  | Failed of (FStar_TypeChecker_Common.prob,Prims.string)
  FStar_Pervasives_Native.tuple2
let (uu___is_Success :solution -> Prims.bool)=
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____750 -> false
let (__proj__Success__item___0
  :solution -> FStar_TypeChecker_Common.deferred)=
  fun projectee  -> match projectee with | Success _0 -> _0
let (uu___is_Failed :solution -> Prims.bool)=
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____768 -> false
let (__proj__Failed__item___0
  :solution ->
     (FStar_TypeChecker_Common.prob,Prims.string)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | Failed _0 -> _0
type variance =
  | COVARIANT
  | CONTRAVARIANT
  | INVARIANT
let (uu___is_COVARIANT :variance -> Prims.bool)=
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____793 -> false
let (uu___is_CONTRAVARIANT :variance -> Prims.bool)=
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____798 -> false
let (uu___is_INVARIANT :variance -> Prims.bool)=
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____803 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let (rel_to_string :FStar_TypeChecker_Common.rel -> Prims.string)=
  fun uu___111_827  ->
    match uu___111_827 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let (term_to_string :FStar_Syntax_Syntax.term -> Prims.string)=
  fun t  ->
    let compact = FStar_Syntax_Print.term_to_string t in
    let detail =
      let uu____834 =
        let uu____835 = FStar_Syntax_Subst.compress t in
        uu____835.FStar_Syntax_Syntax.n in
      match uu____834 with
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let uu____864 = FStar_Syntax_Print.uvar_to_string u in
          let uu____865 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.format2 "%s : %s" uu____864 uu____865
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
             FStar_Syntax_Syntax.pos = uu____868;
             FStar_Syntax_Syntax.vars = uu____869;_},args)
          ->
          let uu____915 = FStar_Syntax_Print.uvar_to_string u in
          let uu____916 = FStar_Syntax_Print.term_to_string ty in
          let uu____917 = FStar_Syntax_Print.args_to_string args in
          FStar_Util.format3 "(%s : %s) %s" uu____915 uu____916 uu____917
      | uu____918 -> "--" in
    let uu____919 = FStar_Syntax_Print.tag_of_term t in
    FStar_Util.format3 "%s (%s)\t%s" compact uu____919 detail
let (prob_to_string
  :FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)=
  fun env  ->
    fun uu___112_927  ->
      match uu___112_927 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____933 =
            let uu____936 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____937 =
              let uu____940 = term_to_string p.FStar_TypeChecker_Common.lhs in
              let uu____941 =
                let uu____944 =
                  let uu____947 =
                    term_to_string p.FStar_TypeChecker_Common.rhs in
                  [uu____947] in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____944 in
              uu____940 :: uu____941 in
            uu____936 :: uu____937 in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s" uu____933
      | FStar_TypeChecker_Common.CProb p ->
          let uu____953 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____954 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\n\t%s \n\t\t%s\n\t%s" uu____953
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____954
let (uvi_to_string :FStar_TypeChecker_Env.env -> uvi -> Prims.string)=
  fun env  ->
    fun uu___113_962  ->
      match uu___113_962 with
      | UNIV (u,t) ->
          let x =
            let uu____966 = FStar_Options.hide_uvar_nums () in
            if uu____966
            then "?"
            else
              (let uu____968 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____968 FStar_Util.string_of_int) in
          let uu____969 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x uu____969
      | TERM ((u,uu____971),t) ->
          let x =
            let uu____978 = FStar_Options.hide_uvar_nums () in
            if uu____978
            then "?"
            else
              (let uu____980 = FStar_Syntax_Unionfind.uvar_id u in
               FStar_All.pipe_right uu____980 FStar_Util.string_of_int) in
          let uu____981 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x uu____981
let (uvis_to_string
  :FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string)=
  fun env  ->
    fun uvis  ->
      let uu____994 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right uu____994 (FStar_String.concat ", ")
let (names_to_string :FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)=
  fun nms  ->
    let uu____1007 =
      let uu____1010 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____1010
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____1007 (FStar_String.concat ", ")
let args_to_string :
  'Auu____1023 .
    (FStar_Syntax_Syntax.term,'Auu____1023) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string=
  fun args  ->
    let uu____1040 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1058  ->
              match uu____1058 with
              | (x,uu____1064) -> FStar_Syntax_Print.term_to_string x)) in
    FStar_All.pipe_right uu____1040 (FStar_String.concat " ")
let (empty_worklist :FStar_TypeChecker_Env.env -> worklist)=
  fun env  ->
    let uu____1071 =
      let uu____1072 = FStar_Options.eager_inference () in
      Prims.op_Negation uu____1072 in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1071;
      smt_ok = true;
      tcenv = env
    }
let (singleton'
  :FStar_TypeChecker_Env.env ->
     FStar_TypeChecker_Common.prob -> Prims.bool -> worklist)=
  fun env  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___144_1091 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___144_1091.wl_deferred);
          ctr = (uu___144_1091.ctr);
          defer_ok = (uu___144_1091.defer_ok);
          smt_ok;
          tcenv = (uu___144_1091.tcenv)
        }
let (singleton
  :FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist)=
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard :
  'Auu____1106 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1106,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist=
  fun env  ->
    fun g  ->
      let uu___145_1127 = empty_worklist env in
      let uu____1128 = FStar_List.map FStar_Pervasives_Native.snd g in
      {
        attempting = uu____1128;
        wl_deferred = (uu___145_1127.wl_deferred);
        ctr = (uu___145_1127.ctr);
        defer_ok = false;
        smt_ok = (uu___145_1127.smt_ok);
        tcenv = (uu___145_1127.tcenv)
      }
let (defer
  :Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist)=
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___146_1145 = wl in
        {
          attempting = (uu___146_1145.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___146_1145.ctr);
          defer_ok = (uu___146_1145.defer_ok);
          smt_ok = (uu___146_1145.smt_ok);
          tcenv = (uu___146_1145.tcenv)
        }
let (attempt
  :FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist)=
  fun probs  ->
    fun wl  ->
      let uu___147_1164 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___147_1164.wl_deferred);
        ctr = (uu___147_1164.ctr);
        defer_ok = (uu___147_1164.defer_ok);
        smt_ok = (uu___147_1164.smt_ok);
        tcenv = (uu___147_1164.tcenv)
      }
let (giveup
  :FStar_TypeChecker_Env.env ->
     Prims.string -> FStar_TypeChecker_Common.prob -> solution)=
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1178 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____1178
         then
           let uu____1179 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1179
         else ());
        Failed (prob, reason)
let (invert_rel
  :FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel)=
  fun uu___114_1184  ->
    match uu___114_1184 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert :
  'Auu____1191 'Auu____1192 .
    ('Auu____1192,'Auu____1191) FStar_TypeChecker_Common.problem ->
      ('Auu____1192,'Auu____1191) FStar_TypeChecker_Common.problem=
  fun p  ->
    let uu___148_1209 = p in
    {
      FStar_TypeChecker_Common.pid =
        (uu___148_1209.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___148_1209.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___148_1209.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___148_1209.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___148_1209.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___148_1209.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___148_1209.FStar_TypeChecker_Common.rank)
    }
let maybe_invert :
  'Auu____1220 'Auu____1221 .
    ('Auu____1221,'Auu____1220) FStar_TypeChecker_Common.problem ->
      ('Auu____1221,'Auu____1220) FStar_TypeChecker_Common.problem=
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
let (maybe_invert_p
  :FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)=
  fun uu___115_1242  ->
    match uu___115_1242 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44)
let (vary_rel
  :FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel)=
  fun rel  ->
    fun uu___116_1268  ->
      match uu___116_1268 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let (p_pid :FStar_TypeChecker_Common.prob -> Prims.int)=
  fun uu___117_1272  ->
    match uu___117_1272 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let (p_rel :FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel)=
  fun uu___118_1286  ->
    match uu___118_1286 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let (p_reason :FStar_TypeChecker_Common.prob -> Prims.string Prims.list)=
  fun uu___119_1302  ->
    match uu___119_1302 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let (p_loc :FStar_TypeChecker_Common.prob -> FStar_Range.range)=
  fun uu___120_1318  ->
    match uu___120_1318 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let (p_guard
  :FStar_TypeChecker_Common.prob ->
     (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2)=
  fun uu___121_1336  ->
    match uu___121_1336 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let (p_scope :FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders)=
  fun uu___122_1354  ->
    match uu___122_1354 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let (p_invert
  :FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)=
  fun uu___123_1368  ->
    match uu___123_1368 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_45  -> FStar_TypeChecker_Common.TProb _0_45) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_46  -> FStar_TypeChecker_Common.CProb _0_46) (invert p)
let (is_top_level_prob :FStar_TypeChecker_Common.prob -> Prims.bool)=
  fun p  ->
    let uu____1391 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____1391 = (Prims.parse_int "1")
let (next_pid :Prims.unit -> Prims.int)=
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____1404  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr
let mk_problem :
  'Auu____1469 'Auu____1470 .
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob ->
        'Auu____1470 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1470 ->
              'Auu____1469 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1470,'Auu____1469)
                    FStar_TypeChecker_Common.problem=
  fun scope  ->
    fun orig  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun reason  ->
                let uu____1507 = next_pid () in
                let uu____1508 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1507;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1508;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let new_problem :
  'Auu____1531 'Auu____1532 .
    FStar_TypeChecker_Env.env ->
      'Auu____1532 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1532 ->
            'Auu____1531 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1532,'Auu____1531)
                    FStar_TypeChecker_Common.problem=
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              fun reason  ->
                let scope = FStar_TypeChecker_Env.all_binders env in
                let uu____1570 = next_pid () in
                let uu____1571 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0 in
                {
                  FStar_TypeChecker_Common.pid = uu____1570;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1571;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = [reason];
                  FStar_TypeChecker_Common.loc = loc;
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
let problem_using_guard :
  'Auu____1592 'Auu____1593 .
    FStar_TypeChecker_Common.prob ->
      'Auu____1593 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1593 ->
            'Auu____1592 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____1593,'Auu____1592) FStar_TypeChecker_Common.problem=
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____1626 = next_pid () in
              {
                FStar_TypeChecker_Common.pid = uu____1626;
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
let guard_on_element :
  'Auu____1637 .
    worklist ->
      ('Auu____1637,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
        FStar_TypeChecker_Common.problem ->
        FStar_Syntax_Syntax.bv ->
          FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ=
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
let (explain
  :FStar_TypeChecker_Env.env ->
     FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)=
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____1690 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____1690
        then
          let uu____1691 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____1692 = prob_to_string env d in
          let uu____1693 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1691 uu____1692 uu____1693 s
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1699 -> failwith "impossible" in
           let uu____1700 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1714 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let uu____1715 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (uu____1714, uu____1715)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1721 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let uu____1722 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (uu____1721, uu____1722) in
           match uu____1700 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let (commit :uvi Prims.list -> Prims.unit)=
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___124_1739  ->
            match uu___124_1739 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1751 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1753),t) -> FStar_Syntax_Util.set_uvar u t))
let (find_term_uvar
  :FStar_Syntax_Syntax.uvar ->
     uvi Prims.list ->
       FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)=
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___125_1775  ->
           match uu___125_1775 with
           | UNIV uu____1778 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1784),t) ->
               let uu____1790 = FStar_Syntax_Unionfind.equiv uv u in
               if uu____1790
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None)
let (find_univ_uvar
  :FStar_Syntax_Syntax.universe_uvar ->
     uvi Prims.list ->
       FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)=
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___126_1812  ->
           match uu___126_1812 with
           | UNIV (u',t) ->
               let uu____1817 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____1817
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1821 -> FStar_Pervasives_Native.None)
let (whnf
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
  fun env  ->
    fun t  ->
      let uu____1830 =
        let uu____1831 = FStar_Syntax_Util.unmeta t in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1831 in
      FStar_Syntax_Subst.compress uu____1830
let (sn
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
  fun env  ->
    fun t  ->
      let uu____1840 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t in
      FStar_Syntax_Subst.compress uu____1840
let norm_arg :
  'Auu____1847 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____1847) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1847)
          FStar_Pervasives_Native.tuple2=
  fun env  ->
    fun t  ->
      let uu____1868 = sn env (FStar_Pervasives_Native.fst t) in
      (uu____1868, (FStar_Pervasives_Native.snd t))
let (sn_binders
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.binders ->
       (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2 Prims.list)=
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1901  ->
              match uu____1901 with
              | (x,imp) ->
                  let uu____1912 =
                    let uu___149_1913 = x in
                    let uu____1914 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___149_1913.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___149_1913.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1914
                    } in
                  (uu____1912, imp)))
let (norm_univ
  :worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)=
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1931 = aux u3 in FStar_Syntax_Syntax.U_succ uu____1931
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1935 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____1935
        | uu____1938 -> u2 in
      let uu____1939 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1939
let normalize_refinement :
  'Auu____1950 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____1950 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ=
  fun steps  ->
    fun env  ->
      fun wl  ->
        fun t0  ->
          FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement :
  'Auu____1975 .
    FStar_TypeChecker_Env.env ->
      'Auu____1975 ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.bv,
                                                                  FStar_Syntax_Syntax.term'
                                                                    FStar_Syntax_Syntax.syntax)
                                                                  FStar_Pervasives_Native.tuple2
                                                                  FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2=
  fun env  ->
    fun wl  ->
      fun t1  ->
        let rec aux norm1 t11 =
          match t11.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm1
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____2080 =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 match uu____2080 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2097;
                     FStar_Syntax_Syntax.vars = uu____2098;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2124 =
                       let uu____2125 = FStar_Syntax_Print.term_to_string tt in
                       let uu____2126 = FStar_Syntax_Print.tag_of_term tt in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2125 uu____2126 in
                     failwith uu____2124)
          | FStar_Syntax_Syntax.Tm_uinst uu____2141 ->
              if norm1
              then (t11, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 let uu____2180 =
                   let uu____2181 = FStar_Syntax_Subst.compress t1' in
                   uu____2181.FStar_Syntax_Syntax.n in
                 match uu____2180 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2198 -> aux true t1'
                 | uu____2205 -> (t11, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2222 ->
              if norm1
              then (t11, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 let uu____2255 =
                   let uu____2256 = FStar_Syntax_Subst.compress t1' in
                   uu____2256.FStar_Syntax_Syntax.n in
                 match uu____2255 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2273 -> aux true t1'
                 | uu____2280 -> (t11, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2297 ->
              if norm1
              then (t11, FStar_Pervasives_Native.None)
              else
                (let t1' =
                   normalize_refinement [FStar_TypeChecker_Normalize.WHNF]
                     env wl t11 in
                 let uu____2344 =
                   let uu____2345 = FStar_Syntax_Subst.compress t1' in
                   uu____2345.FStar_Syntax_Syntax.n in
                 match uu____2344 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2362 -> aux true t1'
                 | uu____2369 -> (t11, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2386 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2403 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2420 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2437 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2454 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2483 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2516 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2549 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____2578 ->
              (t11, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____2617 ->
              let uu____2624 =
                let uu____2625 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2626 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2625 uu____2626 in
              failwith uu____2624
          | FStar_Syntax_Syntax.Tm_ascribed uu____2641 ->
              let uu____2668 =
                let uu____2669 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2670 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2669 uu____2670 in
              failwith uu____2668
          | FStar_Syntax_Syntax.Tm_delayed uu____2685 ->
              let uu____2710 =
                let uu____2711 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2712 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2711 uu____2712 in
              failwith uu____2710
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____2727 =
                let uu____2728 = FStar_Syntax_Print.term_to_string t11 in
                let uu____2729 = FStar_Syntax_Print.tag_of_term t11 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2728 uu____2729 in
              failwith uu____2727 in
        let uu____2744 = whnf env t1 in aux false uu____2744
let (unrefine
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)=
  fun env  ->
    fun t  ->
      let uu____2755 =
        let uu____2770 = empty_worklist env in
        base_and_refinement env uu____2770 t in
      FStar_All.pipe_right uu____2755 FStar_Pervasives_Native.fst
let (trivial_refinement
  :FStar_Syntax_Syntax.term ->
     (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2)=
  fun t  ->
    let uu____2805 = FStar_Syntax_Syntax.null_bv t in
    (uu____2805, FStar_Syntax_Util.t_true)
let as_refinement :
  'Auu____2814 .
    FStar_TypeChecker_Env.env ->
      'Auu____2814 ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2=
  fun env  ->
    fun wl  ->
      fun t  ->
        let uu____2831 = base_and_refinement env wl t in
        match uu____2831 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
let (force_refinement
  :(FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                               FStar_Pervasives_Native.tuple2
                               FStar_Pervasives_Native.option)
     FStar_Pervasives_Native.tuple2 ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)=
  fun uu____2911  ->
    match uu____2911 with
    | (t_base,refopt) ->
        let uu____2938 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base in
        (match uu____2938 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
let (wl_prob_to_string
  :worklist -> FStar_TypeChecker_Common.prob -> Prims.string)=
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob
let (wl_to_string :worklist -> Prims.string)=
  fun wl  ->
    let uu____2973 =
      let uu____2976 =
        let uu____2979 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3002  ->
                  match uu____3002 with | (uu____3009,uu____3010,x) -> x)) in
        FStar_List.append wl.attempting uu____2979 in
      FStar_List.map (wl_prob_to_string wl) uu____2976 in
    FStar_All.pipe_right uu____2973 (FStar_String.concat "\n\t")
let (u_abs
  :FStar_Syntax_Syntax.term ->
     (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list ->
       FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)=
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3038 =
          let uu____3057 =
            let uu____3058 = FStar_Syntax_Subst.compress k in
            uu____3058.FStar_Syntax_Syntax.n in
          match uu____3057 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3123 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____3123)
              else
                (let uu____3149 = FStar_Syntax_Util.abs_formals t in
                 match uu____3149 with
                 | (ys',t1,uu____3178) ->
                     let uu____3183 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____3183))
          | uu____3224 ->
              let uu____3225 =
                let uu____3236 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____3236) in
              ((ys, t), uu____3225) in
        match uu____3038 with
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
                 let uu____3315 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____3315 c in
               FStar_Syntax_Util.abs ys1 t1
                 (FStar_Pervasives_Native.Some
                    (FStar_Syntax_Util.residual_comp_of_comp c1)))
let (solve_prob'
  :Prims.bool ->
     FStar_TypeChecker_Common.prob ->
       FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
         uvi Prims.list -> worklist -> worklist)=
  fun resolve_ok  ->
    fun prob  ->
      fun logical_guard  ->
        fun uvis  ->
          fun wl  ->
            let phi =
              match logical_guard with
              | FStar_Pervasives_Native.None  -> FStar_Syntax_Util.t_true
              | FStar_Pervasives_Native.Some phi -> phi in
            let uu____3348 = p_guard prob in
            match uu____3348 with
            | (uu____3353,uv) ->
                ((let uu____3356 =
                    let uu____3357 = FStar_Syntax_Subst.compress uv in
                    uu____3357.FStar_Syntax_Syntax.n in
                  match uu____3356 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi1 = u_abs k bs phi in
                      ((let uu____3389 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____3389
                        then
                          let uu____3390 =
                            FStar_Util.string_of_int (p_pid prob) in
                          let uu____3391 =
                            FStar_Syntax_Print.term_to_string uv in
                          let uu____3392 =
                            FStar_Syntax_Print.term_to_string phi1 in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3390
                            uu____3391 uu____3392
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____3394 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___150_3397 = wl in
                  {
                    attempting = (uu___150_3397.attempting);
                    wl_deferred = (uu___150_3397.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___150_3397.defer_ok);
                    smt_ok = (uu___150_3397.smt_ok);
                    tcenv = (uu___150_3397.tcenv)
                  }))
let (extend_solution :Prims.int -> uvi Prims.list -> worklist -> worklist)=
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3415 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____3415
         then
           let uu____3416 = FStar_Util.string_of_int pid in
           let uu____3417 =
             let uu____3418 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right uu____3418 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3416 uu____3417
         else ());
        commit sol;
        (let uu___151_3425 = wl in
         {
           attempting = (uu___151_3425.attempting);
           wl_deferred = (uu___151_3425.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___151_3425.defer_ok);
           smt_ok = (uu___151_3425.smt_ok);
           tcenv = (uu___151_3425.tcenv)
         })
let (solve_prob
  :FStar_TypeChecker_Common.prob ->
     FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
       uvi Prims.list -> worklist -> worklist)=
  fun prob  ->
    fun logical_guard  ->
      fun uvis  ->
        fun wl  ->
          let conj_guard1 t g =
            match (t, g) with
            | (uu____3467,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3479 = FStar_Syntax_Util.mk_conj t1 f in
                FStar_Pervasives_Native.Some uu____3479 in
          (let uu____3485 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____3485
           then
             let uu____3486 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____3487 =
               let uu____3488 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right uu____3488 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" uu____3486 uu____3487
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs :
  'b .
    worklist ->
      (FStar_Syntax_Syntax.uvar,'b) FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.typ -> Prims.bool=
  fun wl  ->
    fun uk  ->
      fun t  ->
        let uu____3524 =
          let uu____3531 = FStar_Syntax_Free.uvars t in
          FStar_All.pipe_right uu____3531 FStar_Util.set_elements in
        FStar_All.pipe_right uu____3524
          (FStar_Util.for_some
             (fun uu____3567  ->
                match uu____3567 with
                | (uv,uu____3573) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
let occurs_check :
  'Auu____3586 'Auu____3587 .
    'Auu____3587 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3586)
          FStar_Pervasives_Native.tuple2 ->
          FStar_Syntax_Syntax.typ ->
            (Prims.bool,Prims.string FStar_Pervasives_Native.option)
              FStar_Pervasives_Native.tuple2=
  fun env  ->
    fun wl  ->
      fun uk  ->
        fun t  ->
          let occurs_ok =
            let uu____3619 = occurs wl uk t in Prims.op_Negation uu____3619 in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3626 =
                 let uu____3627 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk) in
                 let uu____3628 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3627 uu____3628 in
               FStar_Pervasives_Native.Some uu____3626) in
          (occurs_ok, msg)
let occurs_and_freevars_check :
  'Auu____3645 'Auu____3646 .
    'Auu____3646 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3645)
          FStar_Pervasives_Native.tuple2 ->
          FStar_Syntax_Syntax.bv FStar_Util.set ->
            FStar_Syntax_Syntax.term ->
              (Prims.bool,Prims.bool,(Prims.string
                                        FStar_Pervasives_Native.option,
                                       FStar_Syntax_Syntax.bv FStar_Util.set,
                                       FStar_Syntax_Syntax.bv FStar_Util.set)
                                       FStar_Pervasives_Native.tuple3)
                FStar_Pervasives_Native.tuple3=
  fun env  ->
    fun wl  ->
      fun uk  ->
        fun fvs  ->
          fun t  ->
            let fvs_t = FStar_Syntax_Free.names t in
            let uu____3700 = occurs_check env wl uk t in
            match uu____3700 with
            | (occurs_ok,msg) ->
                let uu____3731 = FStar_Util.set_is_subset_of fvs_t fvs in
                (occurs_ok, uu____3731, (msg, fvs, fvs_t))
let intersect_vars :
  'Auu____3758 'Auu____3759 .
    (FStar_Syntax_Syntax.bv,'Auu____3759) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3758) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3758) FStar_Pervasives_Native.tuple2
          Prims.list=
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
      let uu____3843 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3897  ->
                fun uu____3898  ->
                  match (uu____3897, uu____3898) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____3979 =
                        let uu____3980 = FStar_Util.set_mem x v1_set in
                        FStar_All.pipe_left Prims.op_Negation uu____3980 in
                      if uu____3979
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                         let uu____4005 =
                           FStar_Util.set_is_subset_of fvs isect_set in
                         if uu____4005
                         then
                           let uu____4018 = FStar_Util.set_add x isect_set in
                           (((x, imp) :: isect), uu____4018)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names)) in
      match uu____3843 with | (isect,uu____4059) -> FStar_List.rev isect
let binders_eq :
  'Auu____4088 'Auu____4089 .
    (FStar_Syntax_Syntax.bv,'Auu____4089) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____4088) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool=
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____4144  ->
              fun uu____4145  ->
                match (uu____4144, uu____4145) with
                | ((a,uu____4163),(b,uu____4165)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt :
  'Auu____4184 'Auu____4185 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____4185) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____4184)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____4184)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option=
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4236 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4250  ->
                      match uu____4250 with
                      | (b,uu____4256) -> FStar_Syntax_Syntax.bv_eq a b)) in
            if uu____4236
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4272 -> FStar_Pervasives_Native.None
let rec (pat_vars
  :FStar_TypeChecker_Env.env ->
     (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 Prims.list ->
       (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
         FStar_Pervasives_Native.tuple2 Prims.list ->
         FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option)=
  fun env  ->
    fun seen  ->
      fun args  ->
        match args with
        | [] -> FStar_Pervasives_Native.Some (FStar_List.rev seen)
        | hd1::rest ->
            let uu____4348 = pat_var_opt env seen hd1 in
            (match uu____4348 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4362 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____4362
                   then
                     let uu____4363 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1) in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4363
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
let (is_flex :FStar_Syntax_Syntax.term -> Prims.bool)=
  fun t  ->
    let uu____4382 =
      let uu____4383 = FStar_Syntax_Subst.compress t in
      uu____4383.FStar_Syntax_Syntax.n in
    match uu____4382 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4386 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4403;
           FStar_Syntax_Syntax.pos = uu____4404;
           FStar_Syntax_Syntax.vars = uu____4405;_},uu____4406)
        -> true
    | uu____4443 -> false
let (destruct_flex_t
  :FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
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
       FStar_Pervasives_Native.tuple4)=
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
           FStar_Syntax_Syntax.pos = uu____4568;
           FStar_Syntax_Syntax.vars = uu____4569;_},args)
        -> (t, uv, k, args)
    | uu____4637 -> failwith "Not a flex-uvar"
let (destruct_flex_pattern
  :FStar_TypeChecker_Env.env ->
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
         FStar_Pervasives_Native.tuple2)=
  fun env  ->
    fun t  ->
      let uu____4716 = destruct_flex_t t in
      match uu____4716 with
      | (t1,uv,k,args) ->
          let uu____4831 = pat_vars env [] args in
          (match uu____4831 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4929 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | HeadMatch
  | FullMatch
let (uu___is_MisMatch :match_result -> Prims.bool)=
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____5011 -> false
let (__proj__MisMatch__item___0
  :match_result ->
     (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,
       FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | MisMatch _0 -> _0
let (uu___is_HeadMatch :match_result -> Prims.bool)=
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____5048 -> false
let (uu___is_FullMatch :match_result -> Prims.bool)=
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5053 -> false
let (head_match :match_result -> match_result)=
  fun uu___127_5057  ->
    match uu___127_5057 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____5072 -> HeadMatch
let (fv_delta_depth
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)=
  fun env  ->
    fun fv  ->
      match fv.FStar_Syntax_Syntax.fv_delta with
      | FStar_Syntax_Syntax.Delta_abstract d ->
          if
            (env.FStar_TypeChecker_Env.curmodule).FStar_Ident.str =
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
          then d
          else FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____5083 ->
          let uu____5084 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____5084 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____5095 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
let rec (delta_depth_of_term
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.term ->
       FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)=
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____5116 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5125 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5152 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5153 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5154 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5171 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5184 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5208) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5214,uu____5215) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5257) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5278;
             FStar_Syntax_Syntax.index = uu____5279;
             FStar_Syntax_Syntax.sort = t2;_},uu____5281)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5288 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5289 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5290 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5303 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5321 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____5321
let rec (head_matches
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> match_result)=
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
            let uu____5345 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____5345
            then FullMatch
            else
              (let uu____5347 =
                 let uu____5356 =
                   let uu____5359 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____5359 in
                 let uu____5360 =
                   let uu____5363 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____5363 in
                 (uu____5356, uu____5360) in
               MisMatch uu____5347)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5369),FStar_Syntax_Syntax.Tm_uinst (g,uu____5371)) ->
            let uu____5380 = head_matches env f g in
            FStar_All.pipe_right uu____5380 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            if c = d
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5389),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5391)) ->
            let uu____5440 = FStar_Syntax_Unionfind.equiv uv uv' in
            if uu____5440
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5447),FStar_Syntax_Syntax.Tm_refine (y,uu____5449)) ->
            let uu____5458 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5458 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5460),uu____5461) ->
            let uu____5466 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____5466 head_match
        | (uu____5467,FStar_Syntax_Syntax.Tm_refine (x,uu____5469)) ->
            let uu____5474 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____5474 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5475,FStar_Syntax_Syntax.Tm_type
           uu____5476) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5477,FStar_Syntax_Syntax.Tm_arrow uu____5478) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5504),FStar_Syntax_Syntax.Tm_app (head',uu____5506))
            ->
            let uu____5547 = head_matches env head1 head' in
            FStar_All.pipe_right uu____5547 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5549),uu____5550) ->
            let uu____5571 = head_matches env head1 t21 in
            FStar_All.pipe_right uu____5571 head_match
        | (uu____5572,FStar_Syntax_Syntax.Tm_app (head1,uu____5574)) ->
            let uu____5595 = head_matches env t11 head1 in
            FStar_All.pipe_right uu____5595 head_match
        | uu____5596 ->
            let uu____5601 =
              let uu____5610 = delta_depth_of_term env t11 in
              let uu____5613 = delta_depth_of_term env t21 in
              (uu____5610, uu____5613) in
            MisMatch uu____5601
let head_matches_delta :
  'Auu____5630 .
    FStar_TypeChecker_Env.env ->
      'Auu____5630 ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (match_result,(FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
                            FStar_Pervasives_Native.tuple2
                            FStar_Pervasives_Native.option)
              FStar_Pervasives_Native.tuple2=
  fun env  ->
    fun wl  ->
      fun t1  ->
        fun t2  ->
          let maybe_inline t =
            let uu____5663 = FStar_Syntax_Util.head_and_args t in
            match uu____5663 with
            | (head1,uu____5681) ->
                let uu____5702 =
                  let uu____5703 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5703.FStar_Syntax_Syntax.n in
                (match uu____5702 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5709 =
                       let uu____5710 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_All.pipe_right uu____5710 FStar_Option.isSome in
                     if uu____5709
                     then
                       let uu____5729 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t in
                       FStar_All.pipe_right uu____5729
                         (fun _0_47  -> FStar_Pervasives_Native.Some _0_47)
                     else FStar_Pervasives_Native.None
                 | uu____5733 -> FStar_Pervasives_Native.None) in
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
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5836)
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5854 =
                     let uu____5863 = maybe_inline t11 in
                     let uu____5866 = maybe_inline t21 in
                     (uu____5863, uu____5866) in
                   match uu____5854 with
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
                (uu____5903,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
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
                (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some
                 d2)
                when d1 = d2 ->
                let uu____5976 = FStar_TypeChecker_Common.decr_delta_depth d1 in
                (match uu____5976 with
                 | FStar_Pervasives_Native.None  -> fail r
                 | FStar_Pervasives_Native.Some d ->
                     let t12 =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d;
                         FStar_TypeChecker_Normalize.WHNF] env wl t11 in
                     let t22 =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d;
                         FStar_TypeChecker_Normalize.WHNF] env wl t21 in
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch
                (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some
                 d2)
                ->
                let d1_greater_than_d2 =
                  FStar_TypeChecker_Common.delta_depth_greater_than d1 d2 in
                let uu____5999 =
                  if d1_greater_than_d2
                  then
                    let t1' =
                      normalize_refinement
                        [FStar_TypeChecker_Normalize.UnfoldUntil d2;
                        FStar_TypeChecker_Normalize.WHNF] env wl t11 in
                    (t1', t21)
                  else
                    (let t2' =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                         FStar_TypeChecker_Normalize.WHNF] env wl t21 in
                     (t11, t2')) in
                (match uu____5999 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6023 -> fail r
            | uu____6032 -> success n_delta r t11 t21 in
          aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
  | C of FStar_Syntax_Syntax.comp
let (uu___is_T :tc -> Prims.bool)=
  fun projectee  -> match projectee with | T _0 -> true | uu____6066 -> false
let (__proj__T__item___0
  :tc ->
     (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                 FStar_Range.range ->
                                   FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | T _0 -> _0
let (uu___is_C :tc -> Prims.bool)=
  fun projectee  -> match projectee with | C _0 -> true | uu____6104 -> false
let (__proj__C__item___0 :tc -> FStar_Syntax_Syntax.comp)=
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let (tc_to_string :tc -> Prims.string)=
  fun uu___128_6118  ->
    match uu___128_6118 with
    | T (t,uu____6120) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
let (generic_kind
  :FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.typ)=
  fun binders  ->
    fun r  ->
      let uu____6138 = FStar_Syntax_Util.type_u () in
      match uu____6138 with
      | (t,uu____6144) ->
          let uu____6145 = new_uvar r binders t in
          FStar_Pervasives_Native.fst uu____6145
let (kind_type
  :FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.typ)=
  fun binders  ->
    fun r  ->
      let uu____6158 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____6158 FStar_Pervasives_Native.fst
let rec (decompose
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.term ->
       (tc Prims.list -> FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term ->
                                                    Prims.bool,(FStar_Syntax_Syntax.binder
                                                                  FStar_Pervasives_Native.option,
                                                                 variance,
                                                                 tc)
                                                                 FStar_Pervasives_Native.tuple3
                                                                 Prims.list)
         FStar_Pervasives_Native.tuple3)=
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      let matches t' =
        let uu____6224 = head_matches env t1 t' in
        match uu____6224 with
        | MisMatch uu____6225 -> false
        | uu____6234 -> true in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6330,imp),T (t2,uu____6333)) -> (t2, imp)
                     | uu____6352 -> failwith "Bad reconstruction") args
                args' in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6419  ->
                    match uu____6419 with
                    | (t2,uu____6433) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6476 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6476 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6551))::tcs2) ->
                       aux
                         (((let uu___152_6586 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___152_6586.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___152_6586.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6604 -> failwith "Bad reconstruction" in
                 aux [] bs1 tcs in
               let rec decompose1 out uu___129_6657 =
                 match uu___129_6657 with
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
               let uu____6774 = decompose1 [] bs1 in
               (rebuild, matches, uu____6774))
      | uu____6823 ->
          let rebuild uu___130_6829 =
            match uu___130_6829 with
            | [] -> t1
            | uu____6832 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
let (un_T :tc -> FStar_Syntax_Syntax.term)=
  fun uu___131_6864  ->
    match uu___131_6864 with
    | T (t,uu____6866) -> t
    | uu____6875 -> failwith "Impossible"
let (arg_of_tc :tc -> FStar_Syntax_Syntax.arg)=
  fun uu___132_6879  ->
    match uu___132_6879 with
    | T (t,uu____6881) -> FStar_Syntax_Syntax.as_arg t
    | uu____6890 -> failwith "Impossible"
let (imitation_sub_probs
  :FStar_TypeChecker_Common.prob ->
     FStar_TypeChecker_Env.env ->
       FStar_Syntax_Syntax.binders ->
         FStar_Syntax_Syntax.args ->
           (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,
             variance,tc) FStar_Pervasives_Native.tuple3 Prims.list ->
             (FStar_TypeChecker_Common.prob Prims.list,tc Prims.list,
               FStar_Syntax_Syntax.formula) FStar_Pervasives_Native.tuple3)=
  fun orig  ->
    fun env  ->
      fun scope  ->
        fun ps  ->
          fun qs  ->
            let r = p_loc orig in
            let rel = p_rel orig in
            let sub_prob scope1 args q =
              match q with
              | (uu____7001,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r in
                  let uu____7026 = new_uvar r scope1 k in
                  (match uu____7026 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7044 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r in
                       let uu____7061 =
                         let uu____7062 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm" in
                         FStar_All.pipe_left
                           (fun _0_48  ->
                              FStar_TypeChecker_Common.TProb _0_48)
                           uu____7062 in
                       ((T (gi_xs, mk_kind)), uu____7061))
              | (uu____7075,uu____7076,C uu____7077) -> failwith "impos" in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7224 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7241;
                         FStar_Syntax_Syntax.vars = uu____7242;_})
                        ->
                        let uu____7265 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7265 with
                         | (T (gi_xs,uu____7289),prob) ->
                             let uu____7299 =
                               let uu____7300 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_49  -> C _0_49)
                                 uu____7300 in
                             (uu____7299, [prob])
                         | uu____7303 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7318;
                         FStar_Syntax_Syntax.vars = uu____7319;_})
                        ->
                        let uu____7342 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type))) in
                        (match uu____7342 with
                         | (T (gi_xs,uu____7366),prob) ->
                             let uu____7376 =
                               let uu____7377 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                               FStar_All.pipe_left (fun _0_50  -> C _0_50)
                                 uu____7377 in
                             (uu____7376, [prob])
                         | uu____7380 -> failwith "impossible")
                    | (uu____7391,uu____7392,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7394;
                         FStar_Syntax_Syntax.vars = uu____7395;_})
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
                        let uu____7526 =
                          let uu____7535 =
                            FStar_List.map (sub_prob scope1 args) components1 in
                          FStar_All.pipe_right uu____7535 FStar_List.unzip in
                        (match uu____7526 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7589 =
                                 let uu____7590 =
                                   let uu____7593 = FStar_List.hd tcs in
                                   FStar_All.pipe_right uu____7593 un_T in
                                 let uu____7594 =
                                   let uu____7603 = FStar_List.tl tcs in
                                   FStar_All.pipe_right uu____7603
                                     (FStar_List.map arg_of_tc) in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7590;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7594;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 } in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7589 in
                             ((C gi_xs), sub_probs))
                    | uu____7612 ->
                        let uu____7625 = sub_prob scope1 args q in
                        (match uu____7625 with
                         | (ktec,prob) -> (ktec, [prob])) in
                  (match uu____7224 with
                   | (tc,probs) ->
                       let uu____7656 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7719,uu____7720),T
                            (t,uu____7722)) ->
                             let b1 =
                               ((let uu___153_7759 = b in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___153_7759.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___153_7759.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp) in
                             let uu____7760 =
                               let uu____7767 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1 in
                               uu____7767 :: args in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7760)
                         | uu____7802 ->
                             (FStar_Pervasives_Native.None, scope1, args) in
                       (match uu____7656 with
                        | (bopt,scope2,args1) ->
                            let uu____7886 = aux scope2 args1 qs2 in
                            (match uu____7886 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____7923 =
                                         let uu____7926 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         f :: uu____7926 in
                                       FStar_Syntax_Util.mk_conj_l uu____7923
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                                       let uu____7949 =
                                         let uu____7952 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f in
                                         let uu____7953 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst)) in
                                         uu____7952 :: uu____7953 in
                                       FStar_Syntax_Util.mk_conj_l uu____7949 in
                                 ((FStar_List.append probs sub_probs), (tc ::
                                   tcs), f1)))) in
            aux scope ps qs
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ,
    FStar_Syntax_Syntax.args) FStar_Pervasives_Native.tuple4
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
    FStar_Pervasives_Native.tuple3
let (rigid_rigid :Prims.int)= Prims.parse_int "0"
let (flex_rigid_eq :Prims.int)= Prims.parse_int "1"
let (flex_refine_inner :Prims.int)= Prims.parse_int "2"
let (flex_refine :Prims.int)= Prims.parse_int "3"
let (flex_rigid :Prims.int)= Prims.parse_int "4"
let (rigid_flex :Prims.int)= Prims.parse_int "5"
let (refine_flex :Prims.int)= Prims.parse_int "6"
let (flex_flex :Prims.int)= Prims.parse_int "7"
let compress_tprob :
  'Auu____8024 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8024)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8024)
          FStar_TypeChecker_Common.problem=
  fun wl  ->
    fun p  ->
      let uu___154_8045 = p in
      let uu____8050 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____8051 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___154_8045.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8050;
        FStar_TypeChecker_Common.relation =
          (uu___154_8045.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8051;
        FStar_TypeChecker_Common.element =
          (uu___154_8045.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___154_8045.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___154_8045.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___154_8045.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___154_8045.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___154_8045.FStar_TypeChecker_Common.rank)
      }
let (compress_prob
  :worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)=
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8065 = compress_tprob wl p1 in
          FStar_All.pipe_right uu____8065
            (fun _0_51  -> FStar_TypeChecker_Common.TProb _0_51)
      | FStar_TypeChecker_Common.CProb uu____8074 -> p
let (rank
  :worklist ->
     FStar_TypeChecker_Common.prob ->
       (Prims.int,FStar_TypeChecker_Common.prob)
         FStar_Pervasives_Native.tuple2)=
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8096 = compress_prob wl pr in
        FStar_All.pipe_right uu____8096 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8106 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____8106 with
           | (lh,uu____8126) ->
               let uu____8147 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____8147 with
                | (rh,uu____8167) ->
                    let uu____8188 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8205,FStar_Syntax_Syntax.Tm_uvar uu____8206)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8243,uu____8244)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8265,FStar_Syntax_Syntax.Tm_uvar uu____8266)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8287,uu____8288)
                          ->
                          let uu____8305 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____8305 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8368 ->
                                    let rank =
                                      let uu____8378 = is_top_level_prob prob in
                                      if uu____8378
                                      then flex_refine
                                      else flex_refine_inner in
                                    let uu____8380 =
                                      let uu___155_8385 = tp in
                                      let uu____8390 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___155_8385.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___155_8385.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___155_8385.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8390;
                                        FStar_TypeChecker_Common.element =
                                          (uu___155_8385.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___155_8385.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___155_8385.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___155_8385.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___155_8385.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___155_8385.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, uu____8380)))
                      | (uu____8405,FStar_Syntax_Syntax.Tm_uvar uu____8406)
                          ->
                          let uu____8423 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____8423 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8486 ->
                                    let uu____8495 =
                                      let uu___156_8502 = tp in
                                      let uu____8507 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___156_8502.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8507;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___156_8502.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___156_8502.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___156_8502.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___156_8502.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___156_8502.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___156_8502.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___156_8502.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___156_8502.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, uu____8495)))
                      | (uu____8528,uu____8529) -> (rigid_rigid, tp) in
                    (match uu____8188 with
                     | (rank,tp1) ->
                         let uu____8548 =
                           FStar_All.pipe_right
                             (let uu___157_8554 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___157_8554.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___157_8554.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___157_8554.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___157_8554.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___157_8554.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___157_8554.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___157_8554.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___157_8554.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___157_8554.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_52  ->
                                FStar_TypeChecker_Common.TProb _0_52) in
                         (rank, uu____8548))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8564 =
            FStar_All.pipe_right
              (let uu___158_8570 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___158_8570.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___158_8570.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___158_8570.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___158_8570.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___158_8570.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___158_8570.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___158_8570.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___158_8570.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___158_8570.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_53  -> FStar_TypeChecker_Common.CProb _0_53) in
          (rigid_rigid, uu____8564)
let (next_prob
  :worklist ->
     (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
       Prims.int) FStar_Pervasives_Native.tuple3)=
  fun wl  ->
    let rec aux uu____8626 probs =
      match uu____8626 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8679 = rank wl hd1 in
               (match uu____8679 with
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
let (is_flex_rigid :Prims.int -> Prims.bool)=
  fun rank1  -> (flex_refine_inner <= rank1) && (rank1 <= flex_rigid)
let (is_rigid_flex :Prims.int -> Prims.bool)=
  fun rank1  -> (rigid_flex <= rank1) && (rank1 <= refine_flex)
type univ_eq_sol =
  | UDeferred of worklist
  | USolved of worklist
  | UFailed of Prims.string
let (uu___is_UDeferred :univ_eq_sol -> Prims.bool)=
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____8789 -> false
let (__proj__UDeferred__item___0 :univ_eq_sol -> worklist)=
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let (uu___is_USolved :univ_eq_sol -> Prims.bool)=
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8803 -> false
let (__proj__USolved__item___0 :univ_eq_sol -> worklist)=
  fun projectee  -> match projectee with | USolved _0 -> _0
let (uu___is_UFailed :univ_eq_sol -> Prims.bool)=
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8817 -> false
let (__proj__UFailed__item___0 :univ_eq_sol -> Prims.string)=
  fun projectee  -> match projectee with | UFailed _0 -> _0
let rec (really_solve_universe_eq
  :Prims.int ->
     worklist ->
       FStar_Syntax_Syntax.universe ->
         FStar_Syntax_Syntax.universe -> univ_eq_sol)=
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
                        let uu____8862 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____8862 with
                        | (k,uu____8868) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8878 -> false)))
            | uu____8879 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____8930 =
                          really_solve_universe_eq pid_orig wl1 u13 u23 in
                        (match uu____8930 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____8933 -> USolved wl1 in
                  aux wl us1 us2
                else
                  (let uu____8943 =
                     let uu____8944 = FStar_Syntax_Print.univ_to_string u12 in
                     let uu____8945 = FStar_Syntax_Print.univ_to_string u22 in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____8944
                       uu____8945 in
                   UFailed uu____8943)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8965 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8965 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8987 =
                        really_solve_universe_eq pid_orig wl1 u u' in
                      (match uu____8987 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed) in
                aux wl us
            | uu____8990 ->
                let uu____8995 =
                  let uu____8996 = FStar_Syntax_Print.univ_to_string u12 in
                  let uu____8997 = FStar_Syntax_Print.univ_to_string u22 in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8996
                    uu____8997 msg in
                UFailed uu____8995 in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8998,uu____8999) ->
              let uu____9000 =
                let uu____9001 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9002 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9001 uu____9002 in
              failwith uu____9000
          | (FStar_Syntax_Syntax.U_unknown ,uu____9003) ->
              let uu____9004 =
                let uu____9005 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9006 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9005 uu____9006 in
              failwith uu____9004
          | (uu____9007,FStar_Syntax_Syntax.U_bvar uu____9008) ->
              let uu____9009 =
                let uu____9010 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9011 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9010 uu____9011 in
              failwith uu____9009
          | (uu____9012,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9013 =
                let uu____9014 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9015 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9014 uu____9015 in
              failwith uu____9013
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9039 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____9039
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u in
              let uu____9061 = occurs_univ v1 u3 in
              if uu____9061
              then
                let uu____9062 =
                  let uu____9063 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9064 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9063 uu____9064 in
                try_umax_components u11 u21 uu____9062
              else
                (let uu____9066 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9066)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____9086 = occurs_univ v1 u3 in
              if uu____9086
              then
                let uu____9087 =
                  let uu____9088 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9089 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9088 uu____9089 in
                try_umax_components u11 u21 uu____9087
              else
                (let uu____9091 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9091)
          | (FStar_Syntax_Syntax.U_max uu____9100,uu____9101) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9107 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9107
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9109,FStar_Syntax_Syntax.U_max uu____9110) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9116 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9116
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9118,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9119,FStar_Syntax_Syntax.U_name
             uu____9120) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9121) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9122) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9123,FStar_Syntax_Syntax.U_succ
             uu____9124) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9125,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
let (solve_universe_eq
  :Prims.int ->
     worklist ->
       FStar_Syntax_Syntax.universe ->
         FStar_Syntax_Syntax.universe -> univ_eq_sol)=
  fun orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          if (wl.tcenv).FStar_TypeChecker_Env.lax_universes
          then USolved wl
          else really_solve_universe_eq orig wl u1 u2
let match_num_binders :
  'a 'b .
    ('a Prims.list,'a Prims.list -> 'b) FStar_Pervasives_Native.tuple2 ->
      ('a Prims.list,'a Prims.list -> 'b) FStar_Pervasives_Native.tuple2 ->
        (('a Prims.list,'b) FStar_Pervasives_Native.tuple2,('a Prims.list,
                                                             'b)
                                                             FStar_Pervasives_Native.tuple2)
          FStar_Pervasives_Native.tuple2=
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
let rec (solve :FStar_TypeChecker_Env.env -> worklist -> solution)=
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
             let uu___159_9634 = probs in
             {
               attempting = tl1;
               wl_deferred = (uu___159_9634.wl_deferred);
               ctr = (uu___159_9634.ctr);
               defer_ok = (uu___159_9634.defer_ok);
               smt_ok = (uu___159_9634.smt_ok);
               tcenv = (uu___159_9634.tcenv)
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
                            let uu___160_9830 = probs in
                            let uu____9831 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9852  ->
                                      match uu____9852 with
                                      | (uu____9859,uu____9860,y) -> y)) in
                            {
                              attempting = uu____9831;
                              wl_deferred = rest;
                              ctr = (uu___160_9830.ctr);
                              defer_ok = (uu___160_9830.defer_ok);
                              smt_ok = (uu___160_9830.smt_ok);
                              tcenv = (uu___160_9830.tcenv)
                            } in
                          solve env uu____9829))))
and (solve_one_universe_eq
  :FStar_TypeChecker_Env.env ->
     FStar_TypeChecker_Common.prob ->
       FStar_Syntax_Syntax.universe ->
         FStar_Syntax_Syntax.universe -> worklist -> solution)=
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
and (solve_maybe_uinsts
  :FStar_TypeChecker_Env.env ->
     FStar_TypeChecker_Common.prob ->
       FStar_Syntax_Syntax.term ->
         FStar_Syntax_Syntax.term -> worklist -> univ_eq_sol)=
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
and (giveup_or_defer
  :FStar_TypeChecker_Env.env ->
     FStar_TypeChecker_Common.prob -> worklist -> Prims.string -> solution)=
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
and (solve_rigid_flex_meet
  :FStar_TypeChecker_Env.env ->
     tprob -> worklist -> worklist FStar_Pervasives_Native.option)=
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
                                 (fun _0_54  ->
                                    FStar_TypeChecker_Common.TProb _0_54)
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
                                                [FStar_TypeChecker_Normalize.WHNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t11 in
                                            let t22 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Normalize.WHNF;
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
                         (fun uu___133_10453  ->
                            match uu___133_10453 with
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
                                  let uu___161_10716 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___161_10716.wl_deferred);
                                    ctr = (uu___161_10716.ctr);
                                    defer_ok = (uu___161_10716.defer_ok);
                                    smt_ok = (uu___161_10716.smt_ok);
                                    tcenv = (uu___161_10716.tcenv)
                                  } in
                                let uu____10717 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10717
                              else ());
                             (let uu____10719 =
                                solve_t env eq_prob
                                  (let uu___162_10721 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___162_10721.wl_deferred);
                                     ctr = (uu___162_10721.ctr);
                                     defer_ok = (uu___162_10721.defer_ok);
                                     smt_ok = (uu___162_10721.smt_ok);
                                     tcenv = (uu___162_10721.tcenv)
                                   }) in
                              match uu____10719 with
                              | Success uu____10724 ->
                                  let wl1 =
                                    let uu___163_10726 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___163_10726.wl_deferred);
                                      ctr = (uu___163_10726.ctr);
                                      defer_ok = (uu___163_10726.defer_ok);
                                      smt_ok = (uu___163_10726.smt_ok);
                                      tcenv = (uu___163_10726.tcenv)
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
and (solve_flex_rigid_join
  :FStar_TypeChecker_Env.env ->
     tprob -> worklist -> worklist FStar_Pervasives_Native.option)=
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
                                              (fun _0_55  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_55) uu____10936 in
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
                                              (fun _0_56  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_56) uu____10973 in
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
                              (fun uu___134_11304  ->
                                 match uu___134_11304 with
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
                                       let uu___164_11617 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___164_11617.wl_deferred);
                                         ctr = (uu___164_11617.ctr);
                                         defer_ok = (uu___164_11617.defer_ok);
                                         smt_ok = (uu___164_11617.smt_ok);
                                         tcenv = (uu___164_11617.tcenv)
                                       } in
                                     let uu____11618 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11618
                                   else ());
                                  (let uu____11620 =
                                     solve_t env eq_prob
                                       (let uu___165_11622 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___165_11622.wl_deferred);
                                          ctr = (uu___165_11622.ctr);
                                          defer_ok =
                                            (uu___165_11622.defer_ok);
                                          smt_ok = (uu___165_11622.smt_ok);
                                          tcenv = (uu___165_11622.tcenv)
                                        }) in
                                   match uu____11620 with
                                   | Success uu____11625 ->
                                       let wl1 =
                                         let uu___166_11627 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___166_11627.wl_deferred);
                                           ctr = (uu___166_11627.ctr);
                                           defer_ok =
                                             (uu___166_11627.defer_ok);
                                           smt_ok = (uu___166_11627.smt_ok);
                                           tcenv = (uu___166_11627.tcenv)
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
and (solve_binders
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.binders ->
       FStar_Syntax_Syntax.binders ->
         FStar_TypeChecker_Common.prob ->
           worklist ->
             (FStar_Syntax_Syntax.binders ->
                FStar_TypeChecker_Env.env ->
                  FStar_Syntax_Syntax.subst_elt Prims.list ->
                    FStar_TypeChecker_Common.prob)
               -> solution)=
  fun env  ->
    fun bs1  ->
      fun bs2  ->
        fun orig  ->
          fun wl  ->
            fun rhs  ->
              let rec aux scope env1 subst1 xs ys =
                match (xs, ys) with
                | ([],[]) ->
                    let rhs_prob = rhs (FStar_List.rev scope) env1 subst1 in
                    ((let uu____11726 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel") in
                      if uu____11726
                      then
                        let uu____11727 = prob_to_string env1 rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11727
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___167_11781 = hd1 in
                      let uu____11782 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___167_11781.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___167_11781.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11782
                      } in
                    let hd21 =
                      let uu___168_11786 = hd2 in
                      let uu____11787 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___168_11786.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___168_11786.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11787
                      } in
                    let prob =
                      let uu____11791 =
                        let uu____11796 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11796 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_57  -> FStar_TypeChecker_Common.TProb _0_57)
                        uu____11791 in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                    let subst2 =
                      let uu____11807 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1 in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11807 in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                    let uu____11811 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1 in
                    (match uu____11811 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11841 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst in
                           let uu____11846 =
                             close_forall env2 [(hd12, imp)] phi in
                           FStar_Syntax_Util.mk_conj uu____11841 uu____11846 in
                         ((let uu____11856 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel") in
                           if uu____11856
                           then
                             let uu____11857 =
                               FStar_Syntax_Print.term_to_string phi1 in
                             let uu____11858 =
                               FStar_Syntax_Print.bv_to_string hd12 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11857 uu____11858
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11881 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____11891 = aux scope env [] bs1 bs2 in
              match uu____11891 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl in
                  solve env (attempt sub_probs wl1)
and (solve_t :FStar_TypeChecker_Env.env -> tprob -> worklist -> solution)=
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____11915 = compress_tprob wl problem in
        solve_t' env uu____11915 wl
and (solve_t' :FStar_TypeChecker_Env.env -> tprob -> worklist -> solution)=
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____11948 = head_matches_delta env1 wl1 t1 t2 in
          match uu____11948 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____11979,uu____11980) ->
                   let rec may_relate head3 =
                     let uu____12005 =
                       let uu____12006 = FStar_Syntax_Subst.compress head3 in
                       uu____12006.FStar_Syntax_Syntax.n in
                     match uu____12005 with
                     | FStar_Syntax_Syntax.Tm_name uu____12009 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____12010 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
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
                     (let uu___169_12129 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12129.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___169_12129.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___169_12129.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12129.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12129.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12129.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12129.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12129.FStar_TypeChecker_Common.rank)
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
                                      base_and_refinement env1 wl1 t1 in
                                    match uu____12258 with
                                    | (base1,refinement1) ->
                                        let uu____12295 =
                                          base_and_refinement env1 wl1 t2 in
                                        (match uu____12295 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____12376 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1 in
                                                  (match uu____12376 with
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
                                                           (fun uu____12398 
                                                              ->
                                                              fun uu____12399
                                                                 ->
                                                                match 
                                                                  (uu____12398,
                                                                    uu____12399)
                                                                with
                                                                | ((a,uu____12417),
                                                                   (a',uu____12419))
                                                                    ->
                                                                    let uu____12428
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
                                                                    _0_58  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_58)
                                                                    uu____12428)
                                                           args1 args2 in
                                                       let formula =
                                                         let uu____12438 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____12438 in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2 in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____12444 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env1
                                                    (let uu___170_12492 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___170_12492.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___170_12492.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___170_12492.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___170_12492.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___170_12492.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___170_12492.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___170_12492.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___170_12492.FStar_TypeChecker_Common.rank)
                                                     }) wl1)))))))) in
        let imitate orig env1 wl1 p =
          let uu____12512 = p in
          match uu____12512 with
          | (((u,k),xs,c),ps,(h,uu____12523,qs)) ->
              let xs1 = sn_binders env1 xs in
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____12605 = imitation_sub_probs orig env1 xs1 ps qs in
              (match uu____12605 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____12628 = h gs_xs in
                     let uu____12629 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_59  -> FStar_Pervasives_Native.Some _0_59) in
                     FStar_Syntax_Util.abs xs1 uu____12628 uu____12629 in
                   ((let uu____12635 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu____12635
                     then
                       let uu____12636 =
                         let uu____12639 =
                           let uu____12640 =
                             FStar_List.map tc_to_string gs_xs in
                           FStar_All.pipe_right uu____12640
                             (FStar_String.concat "\n\t") in
                         let uu____12645 =
                           let uu____12648 =
                             FStar_Syntax_Print.binders_to_string ", " xs1 in
                           let uu____12649 =
                             let uu____12652 =
                               FStar_Syntax_Print.comp_to_string c in
                             let uu____12653 =
                               let uu____12656 =
                                 FStar_Syntax_Print.term_to_string im in
                               let uu____12657 =
                                 let uu____12660 =
                                   FStar_Syntax_Print.tag_of_term im in
                                 let uu____12661 =
                                   let uu____12664 =
                                     let uu____12665 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs in
                                     FStar_All.pipe_right uu____12665
                                       (FStar_String.concat ", ") in
                                   let uu____12670 =
                                     let uu____12673 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula in
                                     [uu____12673] in
                                   uu____12664 :: uu____12670 in
                                 uu____12660 :: uu____12661 in
                               uu____12656 :: uu____12657 in
                             uu____12652 :: uu____12653 in
                           uu____12648 :: uu____12649 in
                         uu____12639 :: uu____12645 in
                       FStar_Util.print
                         "Imitating gs_xs=%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____12636
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1 in
                     solve env1 (attempt sub_probs wl2)))) in
        let imitate' orig env1 wl1 uu___135_12694 =
          match uu___135_12694 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p in
        let project orig env1 wl1 i p =
          let uu____12726 = p in
          match uu____12726 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1 in
              let uu____12817 = FStar_List.nth ps i in
              (match uu____12817 with
               | (pi,uu____12821) ->
                   let uu____12826 = FStar_List.nth xs i in
                   (match uu____12826 with
                    | (xi,uu____12838) ->
                        let rec gs k =
                          let uu____12851 = FStar_Syntax_Util.arrow_formals k in
                          match uu____12851 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____12938)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____12951 = new_uvar r xs k_a in
                                    (match uu____12951 with
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
                                         let uu____12973 = aux subst2 tl1 in
                                         (match uu____12973 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____13000 =
                                                let uu____13003 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1 in
                                                uu____13003 :: gi_xs' in
                                              let uu____13004 =
                                                let uu____13007 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                uu____13007 :: gi_ps' in
                                              (uu____13000, uu____13004))) in
                              aux [] bs in
                        let uu____13012 =
                          let uu____13013 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation uu____13013 in
                        if uu____13012
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____13017 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____13017 with
                           | (g_xs,uu____13029) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let uu____13040 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r in
                                 let uu____13041 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_60  ->
                                        FStar_Pervasives_Native.Some _0_60) in
                                 FStar_Syntax_Util.abs xs uu____13040
                                   uu____13041 in
                               let sub1 =
                                 let uu____13047 =
                                   let uu____13052 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r in
                                   let uu____13055 =
                                     let uu____13058 =
                                       FStar_List.map
                                         (fun uu____13073  ->
                                            match uu____13073 with
                                            | (uu____13082,uu____13083,y) ->
                                                y) qs in
                                     FStar_All.pipe_left h uu____13058 in
                                   mk_problem (p_scope orig) orig uu____13052
                                     (p_rel orig) uu____13055
                                     FStar_Pervasives_Native.None
                                     "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.TProb _0_61)
                                   uu____13047 in
                               ((let uu____13098 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____13098
                                 then
                                   let uu____13099 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let uu____13100 = prob_to_string env1 sub1 in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____13099 uu____13100
                                 else ());
                                (let wl2 =
                                   let uu____13103 =
                                     let uu____13106 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1) in
                                     FStar_Pervasives_Native.Some uu____13106 in
                                   solve_prob orig uu____13103
                                     [TERM (u, proj)] wl1 in
                                 let uu____13115 =
                                   solve env1 (attempt [sub1] wl2) in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_Pervasives_Native.Some _0_62)
                                   uu____13115))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____13146 = lhs in
          match uu____13146 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____13182 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____13182 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____13215 =
                        let uu____13262 = decompose env t2 in
                        (((uv, k_uv), xs, c), ps, uu____13262) in
                      FStar_Pervasives_Native.Some uu____13215
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____13406 =
                           let uu____13413 =
                             let uu____13414 = FStar_Syntax_Subst.compress k in
                             uu____13414.FStar_Syntax_Syntax.n in
                           (uu____13413, args) in
                         match uu____13406 with
                         | (uu____13425,[]) ->
                             let uu____13428 =
                               let uu____13439 =
                                 FStar_Syntax_Syntax.mk_Total k in
                               ([], uu____13439) in
                             FStar_Pervasives_Native.Some uu____13428
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____13460,uu____13461) ->
                             let uu____13482 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____13482 with
                              | (uv1,uv_args) ->
                                  let uu____13525 =
                                    let uu____13526 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____13526.FStar_Syntax_Syntax.n in
                                  (match uu____13525 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____13536) ->
                                       let uu____13561 =
                                         pat_vars env [] uv_args in
                                       (match uu____13561 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____13588  ->
                                                      let uu____13589 =
                                                        let uu____13590 =
                                                          let uu____13591 =
                                                            let uu____13596 =
                                                              let uu____13597
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____13597
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____13596 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____13591 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____13590 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____13589)) in
                                            let c1 =
                                              let uu____13607 =
                                                let uu____13608 =
                                                  let uu____13613 =
                                                    let uu____13614 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____13614
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____13613 in
                                                FStar_Pervasives_Native.fst
                                                  uu____13608 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____13607 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____13627 =
                                                let uu____13630 =
                                                  let uu____13631 =
                                                    let uu____13634 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____13634
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____13631 in
                                                FStar_Pervasives_Native.Some
                                                  uu____13630 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____13627 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____13652 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____13657,uu____13658) ->
                             let uu____13677 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____13677 with
                              | (uv1,uv_args) ->
                                  let uu____13720 =
                                    let uu____13721 =
                                      FStar_Syntax_Subst.compress uv1 in
                                    uu____13721.FStar_Syntax_Syntax.n in
                                  (match uu____13720 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____13731) ->
                                       let uu____13756 =
                                         pat_vars env [] uv_args in
                                       (match uu____13756 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____13783  ->
                                                      let uu____13784 =
                                                        let uu____13785 =
                                                          let uu____13786 =
                                                            let uu____13791 =
                                                              let uu____13792
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  () in
                                                              FStar_All.pipe_right
                                                                uu____13792
                                                                FStar_Pervasives_Native.fst in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____13791 in
                                                          FStar_Pervasives_Native.fst
                                                            uu____13786 in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____13785 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____13784)) in
                                            let c1 =
                                              let uu____13802 =
                                                let uu____13803 =
                                                  let uu____13808 =
                                                    let uu____13809 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____13809
                                                      FStar_Pervasives_Native.fst in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____13808 in
                                                FStar_Pervasives_Native.fst
                                                  uu____13803 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____13802 in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1 in
                                            let uv_sol =
                                              let uu____13822 =
                                                let uu____13825 =
                                                  let uu____13826 =
                                                    let uu____13829 =
                                                      FStar_Syntax_Util.type_u
                                                        () in
                                                    FStar_All.pipe_right
                                                      uu____13829
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____13826 in
                                                FStar_Pervasives_Native.Some
                                                  uu____13825 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____13822 in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____13847 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____13854) ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs1 in
                             if n_xs = n_args
                             then
                               let uu____13895 =
                                 FStar_Syntax_Subst.open_comp xs1 c1 in
                               FStar_All.pipe_right uu____13895
                                 (fun _0_63  ->
                                    FStar_Pervasives_Native.Some _0_63)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____13931 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____13931 with
                                  | (args1,rest) ->
                                      let uu____13960 =
                                        FStar_Syntax_Subst.open_comp xs1 c1 in
                                      (match uu____13960 with
                                       | (xs2,c2) ->
                                           let uu____13973 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest in
                                           FStar_Util.bind_opt uu____13973
                                             (fun uu____13997  ->
                                                match uu____13997 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____14037 =
                                    FStar_Util.first_N n_args xs1 in
                                  match uu____14037 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k.FStar_Syntax_Syntax.pos in
                                      let uu____14105 =
                                        let uu____14110 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____14110 in
                                      FStar_All.pipe_right uu____14105
                                        (fun _0_64  ->
                                           FStar_Pervasives_Native.Some _0_64))
                         | uu____14125 ->
                             let uu____14132 =
                               let uu____14133 =
                                 FStar_Syntax_Print.uvar_to_string uv in
                               let uu____14134 =
                                 FStar_Syntax_Print.term_to_string k in
                               let uu____14135 =
                                 FStar_Syntax_Print.term_to_string k_uv1 in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____14133 uu____14134 uu____14135 in
                             failwith uu____14132 in
                       let uu____14142 = elim k_uv1 ps in
                       FStar_Util.bind_opt uu____14142
                         (fun uu____14197  ->
                            match uu____14197 with
                            | (xs1,c1) ->
                                let uu____14246 =
                                  let uu____14287 = decompose env t2 in
                                  (((uv, k_uv1), xs1, c1), ps, uu____14287) in
                                FStar_Pervasives_Native.Some uu____14246)) in
              let rec imitate_or_project n1 stopt i =
                if (i >= n1) || (FStar_Option.isNone stopt)
                then
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig
                else
                  (let st = FStar_Option.get stopt in
                   let tx = FStar_Syntax_Unionfind.new_transaction () in
                   if i = (- (Prims.parse_int "1"))
                   then
                     let uu____14405 = imitate orig env wl1 st in
                     match uu____14405 with
                     | Failed uu____14410 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____14418 = project orig env wl1 i st in
                      match uu____14418 with
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some (Failed uu____14426) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some sol -> sol)) in
              let check_head fvs1 t21 =
                let uu____14444 = FStar_Syntax_Util.head_and_args t21 in
                match uu____14444 with
                | (hd1,uu____14460) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____14481 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____14494 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____14495 -> true
                     | uu____14512 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1 in
                         let uu____14516 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____14516
                         then true
                         else
                           ((let uu____14519 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____14519
                             then
                               let uu____14520 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____14520
                             else ());
                            false)) in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____14529 =
                    let uu____14532 = FStar_Syntax_Util.head_and_args t21 in
                    FStar_All.pipe_right uu____14532
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____14529 FStar_Syntax_Free.names in
                let uu____14577 = FStar_Util.set_is_empty fvs_hd in
                if uu____14577
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1 in
                   let t21 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t11 in
                   let fvs2 = FStar_Syntax_Free.names t21 in
                   let uu____14588 = occurs_check env wl1 (uv, k_uv) t21 in
                   (match uu____14588 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____14601 =
                            let uu____14602 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " uu____14602 in
                          giveup_or_defer1 orig uu____14601
                        else
                          (let uu____14604 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____14604
                           then
                             let uu____14605 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____14605
                              then
                                let uu____14606 = subterms args_lhs in
                                imitate' orig env wl1 uu____14606
                              else
                                ((let uu____14611 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____14611
                                  then
                                    let uu____14612 =
                                      FStar_Syntax_Print.term_to_string t11 in
                                    let uu____14613 = names_to_string fvs1 in
                                    let uu____14614 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____14612 uu____14613 uu____14614
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____14621 ->
                                        let uu____14622 = sn_binders env vars in
                                        u_abs k_uv uu____14622 t21 in
                                  let wl2 =
                                    solve_prob orig
                                      FStar_Pervasives_Native.None
                                      [TERM ((uv, k_uv), sol)] wl1 in
                                  solve env wl2)))
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
                               (let uu____14636 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21) in
                                if uu____14636
                                then
                                  ((let uu____14638 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____14638
                                    then
                                      let uu____14639 =
                                        FStar_Syntax_Print.term_to_string t11 in
                                      let uu____14640 = names_to_string fvs1 in
                                      let uu____14641 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____14639 uu____14640 uu____14641
                                    else ());
                                   (let uu____14643 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs)
                                      uu____14643 (- (Prims.parse_int "1"))))
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
                     (let uu____14654 =
                        let uu____14655 = FStar_Syntax_Free.names t1 in
                        check_head uu____14655 t2 in
                      if uu____14654
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____14660 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____14660
                          then
                            let uu____14661 =
                              FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____14661
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____14664 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____14664 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____14719 =
               match uu____14719 with
               | (t,u,k,args) ->
                   let k1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta] env k in
                   let uu____14769 = FStar_Syntax_Util.arrow_formals k1 in
                   (match uu____14769 with
                    | (all_formals,uu____14787) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____14950  ->
                                        match uu____14950 with
                                        | (x,imp) ->
                                            let uu____14961 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (uu____14961, imp))) in
                              let pattern_vars1 = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____14974 = FStar_Syntax_Util.type_u () in
                                match uu____14974 with
                                | (t1,uu____14980) ->
                                    let uu____14981 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1 in
                                    FStar_Pervasives_Native.fst uu____14981 in
                              let uu____14986 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk in
                              (match uu____14986 with
                               | (t',tm_u1) ->
                                   let uu____14997 = destruct_flex_t t' in
                                   (match uu____14997 with
                                    | (uu____15032,u1,k11,uu____15035) ->
                                        let sol =
                                          let uu____15081 =
                                            let uu____15090 =
                                              u_abs k1 all_formals t' in
                                            ((u, k1), uu____15090) in
                                          TERM uu____15081 in
                                        let t_app =
                                          FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                            pat_args1
                                            FStar_Pervasives_Native.None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k11, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____15190 = pat_var_opt env pat_args hd1 in
                              (match uu____15190 with
                               | FStar_Pervasives_Native.None  ->
                                   aux pat_args pattern_vars pattern_var_set
                                     formals1 tl1
                               | FStar_Pervasives_Native.Some y ->
                                   let maybe_pat =
                                     match xs_opt with
                                     | FStar_Pervasives_Native.None  -> true
                                     | FStar_Pervasives_Native.Some xs ->
                                         FStar_All.pipe_right xs
                                           (FStar_Util.for_some
                                              (fun uu____15247  ->
                                                 match uu____15247 with
                                                 | (x,uu____15253) ->
                                                     FStar_Syntax_Syntax.bv_eq
                                                       x
                                                       (FStar_Pervasives_Native.fst
                                                          y))) in
                                   if Prims.op_Negation maybe_pat
                                   then
                                     aux pat_args pattern_vars
                                       pattern_var_set formals1 tl1
                                   else
                                     (let fvs =
                                        FStar_Syntax_Free.names
                                          (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort in
                                      let uu____15262 =
                                        let uu____15263 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set in
                                        Prims.op_Negation uu____15263 in
                                      if uu____15262
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____15269 =
                                           FStar_Util.set_add
                                             (FStar_Pervasives_Native.fst
                                                formal) pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____15269 formals1
                                           tl1)))
                          | uu____15280 -> failwith "Impossible" in
                        let uu____15301 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] uu____15301 all_formals args) in
             let solve_both_pats wl1 uu____15366 uu____15367 r =
               match (uu____15366, uu____15367) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____15565 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys) in
                   if uu____15565
                   then
                     let uu____15566 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                     solve env uu____15566
                   else
                     (let xs1 = sn_binders env xs in
                      let ys1 = sn_binders env ys in
                      let zs = intersect_vars xs1 ys1 in
                      (let uu____15590 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____15590
                       then
                         let uu____15591 =
                           FStar_Syntax_Print.binders_to_string ", " xs1 in
                         let uu____15592 =
                           FStar_Syntax_Print.binders_to_string ", " ys1 in
                         let uu____15593 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let uu____15594 =
                           FStar_Syntax_Print.term_to_string k1 in
                         let uu____15595 =
                           FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____15591 uu____15592 uu____15593 uu____15594
                           uu____15595
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2 in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let uu____15655 =
                             FStar_Syntax_Util.subst_of_list xs2 args in
                           FStar_Syntax_Subst.subst uu____15655 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____15669 =
                                FStar_Util.first_N args_len xs2 in
                              match uu____15669 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____15723 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____15723 in
                                  let uu____15726 =
                                    FStar_Syntax_Util.subst_of_list xs3 args in
                                  FStar_Syntax_Subst.subst uu____15726 k3)
                           else
                             (let uu____15730 =
                                let uu____15731 =
                                  FStar_Syntax_Print.term_to_string k in
                                let uu____15732 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2 in
                                let uu____15733 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____15731 uu____15732 uu____15733 in
                              failwith uu____15730) in
                       let uu____15734 =
                         let uu____15743 =
                           let uu____15756 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1 in
                           FStar_Syntax_Util.arrow_formals uu____15756 in
                         match uu____15743 with
                         | (bs,k1') ->
                             let uu____15783 =
                               let uu____15796 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2 in
                               FStar_Syntax_Util.arrow_formals uu____15796 in
                             (match uu____15783 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let uu____15826 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65)
                                      uu____15826 in
                                  let uu____15835 =
                                    let uu____15840 =
                                      let uu____15841 =
                                        FStar_Syntax_Subst.compress k1' in
                                      uu____15841.FStar_Syntax_Syntax.n in
                                    let uu____15844 =
                                      let uu____15845 =
                                        FStar_Syntax_Subst.compress k2' in
                                      uu____15845.FStar_Syntax_Syntax.n in
                                    (uu____15840, uu____15844) in
                                  (match uu____15835 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____15856,uu____15857) ->
                                       (k1', [sub_prob])
                                   | (uu____15862,FStar_Syntax_Syntax.Tm_type
                                      uu____15863) -> (k2', [sub_prob])
                                   | uu____15868 ->
                                       let uu____15873 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____15873 with
                                        | (t,uu____15887) ->
                                            let uu____15888 = new_uvar r zs t in
                                            (match uu____15888 with
                                             | (k_zs,uu____15902) ->
                                                 let kprob =
                                                   let uu____15904 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs
                                                       FStar_Pervasives_Native.None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_66  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_66) uu____15904 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____15734 with
                       | (k_u',sub_probs) ->
                           let uu____15925 =
                             let uu____15936 =
                               let uu____15937 = new_uvar r zs k_u' in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____15937 in
                             let uu____15946 =
                               let uu____15949 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs1 uu____15949 in
                             let uu____15952 =
                               let uu____15955 =
                                 FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys1 uu____15955 in
                             (uu____15936, uu____15946, uu____15952) in
                           (match uu____15925 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs in
                                let uu____15974 =
                                  occurs_check env wl1 (u1, k1) sub1 in
                                (match uu____15974 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____15993 =
                                          FStar_Syntax_Unionfind.equiv u1 u2 in
                                        if uu____15993
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1 in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs in
                                           let uu____15997 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2 in
                                           match uu____15997 with
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
             let solve_one_pat uu____16050 uu____16051 =
               match (uu____16050, uu____16051) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____16169 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____16169
                     then
                       let uu____16170 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____16171 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____16170 uu____16171
                     else ());
                    (let uu____16173 = FStar_Syntax_Unionfind.equiv u1 u2 in
                     if uu____16173
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16192  ->
                              fun uu____16193  ->
                                match (uu____16192, uu____16193) with
                                | ((a,uu____16211),(t21,uu____16213)) ->
                                    let uu____16222 =
                                      let uu____16227 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig
                                        uu____16227
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index" in
                                    FStar_All.pipe_right uu____16222
                                      (fun _0_67  ->
                                         FStar_TypeChecker_Common.TProb _0_67))
                           xs args2 in
                       let guard =
                         let uu____16233 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs in
                         FStar_Syntax_Util.mk_conj_l uu____16233 in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t21 in
                        let uu____16248 = occurs_check env wl (u1, k1) t21 in
                        match uu____16248 with
                        | (occurs_ok,uu____16256) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____16264 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____16264
                            then
                              let sol =
                                let uu____16266 =
                                  let uu____16275 = u_abs k1 xs t21 in
                                  ((u1, k1), uu____16275) in
                                TERM uu____16266 in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl in
                              solve env wl1
                            else
                              (let uu____16282 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____16282
                               then
                                 let uu____16283 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2) in
                                 match uu____16283 with
                                 | (sol,(uu____16301,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____16315 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____16315
                                       then
                                         let uu____16316 =
                                           uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16316
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16323 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint")))) in
             let uu____16325 = lhs in
             match uu____16325 with
             | (t1,u1,k1,args1) ->
                 let uu____16330 = rhs in
                 (match uu____16330 with
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
                       | uu____16370 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16380 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1) in
                              match uu____16380 with
                              | (sol,uu____16392) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____16395 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____16395
                                    then
                                      let uu____16396 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16396
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16403 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____16405 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____16405
        then
          let uu____16406 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____16406
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____16410 = FStar_Util.physical_equality t1 t2 in
           if uu____16410
           then
             let uu____16411 =
               solve_prob orig FStar_Pervasives_Native.None [] wl in
             solve env uu____16411
           else
             ((let uu____16414 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____16414
               then
                 let uu____16415 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" uu____16415
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_ascribed uu____16418,uu____16419) ->
                   let uu____16446 =
                     let uu___171_16447 = problem in
                     let uu____16448 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___171_16447.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16448;
                       FStar_TypeChecker_Common.relation =
                         (uu___171_16447.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___171_16447.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___171_16447.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___171_16447.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___171_16447.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___171_16447.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___171_16447.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___171_16447.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16446 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____16449,uu____16450) ->
                   let uu____16457 =
                     let uu___171_16458 = problem in
                     let uu____16459 = FStar_Syntax_Util.unmeta t1 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___171_16458.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16459;
                       FStar_TypeChecker_Common.relation =
                         (uu___171_16458.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___171_16458.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___171_16458.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___171_16458.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___171_16458.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___171_16458.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___171_16458.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___171_16458.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16457 wl
               | (uu____16460,FStar_Syntax_Syntax.Tm_ascribed uu____16461) ->
                   let uu____16488 =
                     let uu___172_16489 = problem in
                     let uu____16490 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___172_16489.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___172_16489.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___172_16489.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16490;
                       FStar_TypeChecker_Common.element =
                         (uu___172_16489.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___172_16489.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___172_16489.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___172_16489.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___172_16489.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___172_16489.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16488 wl
               | (uu____16491,FStar_Syntax_Syntax.Tm_meta uu____16492) ->
                   let uu____16499 =
                     let uu___172_16500 = problem in
                     let uu____16501 = FStar_Syntax_Util.unmeta t2 in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___172_16500.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___172_16500.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___172_16500.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16501;
                       FStar_TypeChecker_Common.element =
                         (uu___172_16500.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___172_16500.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___172_16500.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___172_16500.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___172_16500.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___172_16500.FStar_TypeChecker_Common.rank)
                     } in
                   solve_t' env uu____16499 wl
               | (FStar_Syntax_Syntax.Tm_bvar uu____16502,uu____16503) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____16504,FStar_Syntax_Syntax.Tm_bvar uu____16505) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___136_16560 =
                     match uu___136_16560 with
                     | [] -> c
                     | bs ->
                         let uu____16582 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos in
                         FStar_Syntax_Syntax.mk_Total uu____16582 in
                   let uu____16591 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____16591 with
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
                                   let uu____16733 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____16733
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let uu____16735 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_68  ->
                                      FStar_TypeChecker_Common.CProb _0_68)
                                   uu____16735))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___137_16811 =
                     match uu___137_16811 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____16845 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____16845 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____16981 =
                                   let uu____16986 =
                                     FStar_Syntax_Subst.subst subst1 tbody11 in
                                   let uu____16987 =
                                     FStar_Syntax_Subst.subst subst1 tbody21 in
                                   mk_problem scope orig uu____16986
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____16987 FStar_Pervasives_Native.None
                                     "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____16981))
               | (FStar_Syntax_Syntax.Tm_abs uu____16992,uu____16993) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17018 -> true
                     | uu____17035 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____17069 =
                     let uu____17086 = maybe_eta t1 in
                     let uu____17093 = maybe_eta t2 in
                     (uu____17086, uu____17093) in
                   (match uu____17069 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___173_17135 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___173_17135.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___173_17135.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___173_17135.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___173_17135.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___173_17135.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___173_17135.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___173_17135.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___173_17135.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17158 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17158
                        then
                          let uu____17159 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17159 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17187 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17187
                        then
                          let uu____17188 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17188 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____17196 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17213,FStar_Syntax_Syntax.Tm_abs uu____17214) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17239 -> true
                     | uu____17256 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3) in
                   let uu____17290 =
                     let uu____17307 = maybe_eta t1 in
                     let uu____17314 = maybe_eta t2 in
                     (uu____17307, uu____17314) in
                   (match uu____17290 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___173_17356 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___173_17356.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___173_17356.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___173_17356.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___173_17356.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___173_17356.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___173_17356.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___173_17356.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___173_17356.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17379 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17379
                        then
                          let uu____17380 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17380 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17408 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____17408
                        then
                          let uu____17409 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig uu____17409 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____17417 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____17434,FStar_Syntax_Syntax.Tm_refine uu____17435) ->
                   let uu____17448 = as_refinement env wl t1 in
                   (match uu____17448 with
                    | (x1,phi1) ->
                        let uu____17455 = as_refinement env wl t2 in
                        (match uu____17455 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____17463 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_70  ->
                                    FStar_TypeChecker_Common.TProb _0_70)
                                 uu____17463 in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)] in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1 in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2 in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11 in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____17501 = imp phi12 phi22 in
                               FStar_All.pipe_right uu____17501
                                 (guard_on_element wl problem x11) in
                             let fallback uu____17505 =
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
                                 let uu____17511 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____17511 impl in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl in
                               solve env1 (attempt [base_prob] wl1) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____17520 =
                                   let uu____17525 =
                                     let uu____17526 =
                                       FStar_Syntax_Syntax.mk_binder x11 in
                                     uu____17526 :: (p_scope orig) in
                                   mk_problem uu____17525 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_71  ->
                                      FStar_TypeChecker_Common.TProb _0_71)
                                   uu____17520 in
                               let uu____17531 =
                                 solve env1
                                   (let uu___174_17533 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___174_17533.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___174_17533.smt_ok);
                                      tcenv = (uu___174_17533.tcenv)
                                    }) in
                               (match uu____17531 with
                                | Failed uu____17540 -> fallback ()
                                | Success uu____17545 ->
                                    let guard =
                                      let uu____17549 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst in
                                      let uu____17554 =
                                        let uu____17555 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst in
                                        FStar_All.pipe_right uu____17555
                                          (guard_on_element wl problem x11) in
                                      FStar_Syntax_Util.mk_conj uu____17549
                                        uu____17554 in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl in
                                    let wl2 =
                                      let uu___175_17564 = wl1 in
                                      {
                                        attempting =
                                          (uu___175_17564.attempting);
                                        wl_deferred =
                                          (uu___175_17564.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___175_17564.defer_ok);
                                        smt_ok = (uu___175_17564.smt_ok);
                                        tcenv = (uu___175_17564.tcenv)
                                      } in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17566,FStar_Syntax_Syntax.Tm_uvar uu____17567) ->
                   let uu____17600 = destruct_flex_t t1 in
                   let uu____17601 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17600 uu____17601
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17602;
                     FStar_Syntax_Syntax.pos = uu____17603;
                     FStar_Syntax_Syntax.vars = uu____17604;_},uu____17605),FStar_Syntax_Syntax.Tm_uvar
                  uu____17606) ->
                   let uu____17659 = destruct_flex_t t1 in
                   let uu____17660 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17659 uu____17660
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17661,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17662;
                     FStar_Syntax_Syntax.pos = uu____17663;
                     FStar_Syntax_Syntax.vars = uu____17664;_},uu____17665))
                   ->
                   let uu____17718 = destruct_flex_t t1 in
                   let uu____17719 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17718 uu____17719
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17720;
                     FStar_Syntax_Syntax.pos = uu____17721;
                     FStar_Syntax_Syntax.vars = uu____17722;_},uu____17723),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17724;
                     FStar_Syntax_Syntax.pos = uu____17725;
                     FStar_Syntax_Syntax.vars = uu____17726;_},uu____17727))
                   ->
                   let uu____17800 = destruct_flex_t t1 in
                   let uu____17801 = destruct_flex_t t2 in
                   flex_flex1 orig uu____17800 uu____17801
               | (FStar_Syntax_Syntax.Tm_uvar uu____17802,uu____17803) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____17820 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____17820 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17827;
                     FStar_Syntax_Syntax.pos = uu____17828;
                     FStar_Syntax_Syntax.vars = uu____17829;_},uu____17830),uu____17831)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____17868 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig uu____17868 t2 wl
               | (uu____17875,FStar_Syntax_Syntax.Tm_uvar uu____17876) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____17893,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17894;
                     FStar_Syntax_Syntax.pos = uu____17895;
                     FStar_Syntax_Syntax.vars = uu____17896;_},uu____17897))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17934,FStar_Syntax_Syntax.Tm_type uu____17935) ->
                   solve_t' env
                     (let uu___176_17953 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_17953.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___176_17953.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___176_17953.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___176_17953.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_17953.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_17953.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_17953.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_17953.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_17953.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____17954;
                     FStar_Syntax_Syntax.pos = uu____17955;
                     FStar_Syntax_Syntax.vars = uu____17956;_},uu____17957),FStar_Syntax_Syntax.Tm_type
                  uu____17958) ->
                   solve_t' env
                     (let uu___176_17996 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_17996.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___176_17996.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___176_17996.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___176_17996.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_17996.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_17996.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_17996.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_17996.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_17996.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____17997,FStar_Syntax_Syntax.Tm_arrow uu____17998) ->
                   solve_t' env
                     (let uu___176_18028 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_18028.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___176_18028.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___176_18028.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___176_18028.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_18028.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_18028.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_18028.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_18028.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_18028.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18029;
                     FStar_Syntax_Syntax.pos = uu____18030;
                     FStar_Syntax_Syntax.vars = uu____18031;_},uu____18032),FStar_Syntax_Syntax.Tm_arrow
                  uu____18033) ->
                   solve_t' env
                     (let uu___176_18083 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_18083.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___176_18083.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___176_18083.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___176_18083.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_18083.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_18083.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_18083.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_18083.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_18083.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18084,uu____18085) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18104 =
                        let uu____18105 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18105 in
                      if uu____18104
                      then
                        let uu____18106 =
                          FStar_All.pipe_left
                            (fun _0_72  ->
                               FStar_TypeChecker_Common.TProb _0_72)
                            (let uu___177_18112 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___177_18112.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___177_18112.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___177_18112.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___177_18112.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___177_18112.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___177_18112.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___177_18112.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___177_18112.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___177_18112.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18113 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18106 uu____18113 t2
                          wl
                      else
                        (let uu____18121 = base_and_refinement env wl t2 in
                         match uu____18121 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18164 =
                                    FStar_All.pipe_left
                                      (fun _0_73  ->
                                         FStar_TypeChecker_Common.TProb _0_73)
                                      (let uu___178_18170 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___178_18170.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___178_18170.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___178_18170.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___178_18170.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___178_18170.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___178_18170.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___178_18170.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___178_18170.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___178_18170.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18171 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18164
                                    uu____18171 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___179_18191 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___179_18191.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___179_18191.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18194 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      uu____18194 in
                                  let guard =
                                    let uu____18206 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18206
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18214;
                     FStar_Syntax_Syntax.pos = uu____18215;
                     FStar_Syntax_Syntax.vars = uu____18216;_},uu____18217),uu____18218)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____18257 =
                        let uu____18258 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation uu____18258 in
                      if uu____18257
                      then
                        let uu____18259 =
                          FStar_All.pipe_left
                            (fun _0_75  ->
                               FStar_TypeChecker_Common.TProb _0_75)
                            (let uu___177_18265 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___177_18265.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___177_18265.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___177_18265.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___177_18265.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___177_18265.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___177_18265.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___177_18265.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___177_18265.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___177_18265.FStar_TypeChecker_Common.rank)
                             }) in
                        let uu____18266 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false uu____18259 uu____18266 t2
                          wl
                      else
                        (let uu____18274 = base_and_refinement env wl t2 in
                         match uu____18274 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18317 =
                                    FStar_All.pipe_left
                                      (fun _0_76  ->
                                         FStar_TypeChecker_Common.TProb _0_76)
                                      (let uu___178_18323 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___178_18323.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___178_18323.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___178_18323.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___178_18323.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___178_18323.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___178_18323.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___178_18323.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___178_18323.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___178_18323.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let uu____18324 =
                                    destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false uu____18317
                                    uu____18324 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___179_18344 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___179_18344.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___179_18344.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl =
                                    guard_on_element wl problem y' phi in
                                  let base_prob =
                                    let uu____18347 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_77  ->
                                         FStar_TypeChecker_Common.TProb _0_77)
                                      uu____18347 in
                                  let guard =
                                    let uu____18359 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst in
                                    FStar_Syntax_Util.mk_conj uu____18359
                                      impl in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18367,FStar_Syntax_Syntax.Tm_uvar uu____18368) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18386 = base_and_refinement env wl t1 in
                      match uu____18386 with
                      | (t_base,uu____18402) ->
                          solve_t env
                            (let uu___180_18424 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___180_18424.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___180_18424.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___180_18424.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___180_18424.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___180_18424.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___180_18424.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___180_18424.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___180_18424.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18427,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18428;
                     FStar_Syntax_Syntax.pos = uu____18429;
                     FStar_Syntax_Syntax.vars = uu____18430;_},uu____18431))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18469 = base_and_refinement env wl t1 in
                      match uu____18469 with
                      | (t_base,uu____18485) ->
                          solve_t env
                            (let uu___180_18507 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___180_18507.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___180_18507.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___180_18507.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___180_18507.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___180_18507.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___180_18507.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___180_18507.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___180_18507.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____18510,uu____18511) ->
                   let t21 =
                     let uu____18521 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement uu____18521 in
                   solve_t env
                     (let uu___181_18545 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___181_18545.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___181_18545.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___181_18545.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___181_18545.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___181_18545.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___181_18545.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___181_18545.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___181_18545.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___181_18545.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____18546,FStar_Syntax_Syntax.Tm_refine uu____18547) ->
                   let t11 =
                     let uu____18557 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement uu____18557 in
                   solve_t env
                     (let uu___182_18581 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___182_18581.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___182_18581.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___182_18581.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___182_18581.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___182_18581.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___182_18581.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___182_18581.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___182_18581.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___182_18581.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____18584,uu____18585) ->
                   let head1 =
                     let uu____18611 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18611
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18655 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18655
                       FStar_Pervasives_Native.fst in
                   let uu____18696 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18696
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18711 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18711
                      then
                        let guard =
                          let uu____18723 =
                            let uu____18724 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18724 = FStar_Syntax_Util.Equal in
                          if uu____18723
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18728 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____18728) in
                        let uu____18731 = solve_prob orig guard [] wl in
                        solve env uu____18731
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____18734,uu____18735) ->
                   let head1 =
                     let uu____18745 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18745
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18789 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18789
                       FStar_Pervasives_Native.fst in
                   let uu____18830 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18830
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18845 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18845
                      then
                        let guard =
                          let uu____18857 =
                            let uu____18858 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18858 = FStar_Syntax_Util.Equal in
                          if uu____18857
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18862 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____18862) in
                        let uu____18865 = solve_prob orig guard [] wl in
                        solve env uu____18865
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____18868,uu____18869) ->
                   let head1 =
                     let uu____18873 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____18873
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____18917 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____18917
                       FStar_Pervasives_Native.fst in
                   let uu____18958 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____18958
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____18973 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____18973
                      then
                        let guard =
                          let uu____18985 =
                            let uu____18986 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____18986 = FStar_Syntax_Util.Equal in
                          if uu____18985
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____18990 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____18990) in
                        let uu____18993 = solve_prob orig guard [] wl in
                        solve env uu____18993
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____18996,uu____18997) ->
                   let head1 =
                     let uu____19001 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19001
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19045 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19045
                       FStar_Pervasives_Native.fst in
                   let uu____19086 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19086
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19101 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19101
                      then
                        let guard =
                          let uu____19113 =
                            let uu____19114 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19114 = FStar_Syntax_Util.Equal in
                          if uu____19113
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19118 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19118) in
                        let uu____19121 = solve_prob orig guard [] wl in
                        solve env uu____19121
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____19124,uu____19125) ->
                   let head1 =
                     let uu____19129 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19129
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19173 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19173
                       FStar_Pervasives_Native.fst in
                   let uu____19214 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19214
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19229 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19229
                      then
                        let guard =
                          let uu____19241 =
                            let uu____19242 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19242 = FStar_Syntax_Util.Equal in
                          if uu____19241
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19246 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____19246) in
                        let uu____19249 = solve_prob orig guard [] wl in
                        solve env uu____19249
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19252,uu____19253) ->
                   let head1 =
                     let uu____19271 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19271
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19315 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19315
                       FStar_Pervasives_Native.fst in
                   let uu____19356 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19356
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19371 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19371
                      then
                        let guard =
                          let uu____19383 =
                            let uu____19384 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19384 = FStar_Syntax_Util.Equal in
                          if uu____19383
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19388 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____19388) in
                        let uu____19391 = solve_prob orig guard [] wl in
                        solve env uu____19391
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19394,FStar_Syntax_Syntax.Tm_match uu____19395) ->
                   let head1 =
                     let uu____19421 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19421
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19465 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19465
                       FStar_Pervasives_Native.fst in
                   let uu____19506 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19506
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19521 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19521
                      then
                        let guard =
                          let uu____19533 =
                            let uu____19534 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19534 = FStar_Syntax_Util.Equal in
                          if uu____19533
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19538 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____19538) in
                        let uu____19541 = solve_prob orig guard [] wl in
                        solve env uu____19541
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19544,FStar_Syntax_Syntax.Tm_uinst uu____19545) ->
                   let head1 =
                     let uu____19555 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19555
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19599 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19599
                       FStar_Pervasives_Native.fst in
                   let uu____19640 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19640
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19655 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19655
                      then
                        let guard =
                          let uu____19667 =
                            let uu____19668 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19668 = FStar_Syntax_Util.Equal in
                          if uu____19667
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19672 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____19672) in
                        let uu____19675 = solve_prob orig guard [] wl in
                        solve env uu____19675
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19678,FStar_Syntax_Syntax.Tm_name uu____19679) ->
                   let head1 =
                     let uu____19683 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19683
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19727 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19727
                       FStar_Pervasives_Native.fst in
                   let uu____19768 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19768
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19783 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19783
                      then
                        let guard =
                          let uu____19795 =
                            let uu____19796 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19796 = FStar_Syntax_Util.Equal in
                          if uu____19795
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19800 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____19800) in
                        let uu____19803 = solve_prob orig guard [] wl in
                        solve env uu____19803
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19806,FStar_Syntax_Syntax.Tm_constant uu____19807) ->
                   let head1 =
                     let uu____19811 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19811
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19855 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19855
                       FStar_Pervasives_Native.fst in
                   let uu____19896 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____19896
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____19911 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____19911
                      then
                        let guard =
                          let uu____19923 =
                            let uu____19924 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____19924 = FStar_Syntax_Util.Equal in
                          if uu____19923
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19928 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____19928) in
                        let uu____19931 = solve_prob orig guard [] wl in
                        solve env uu____19931
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19934,FStar_Syntax_Syntax.Tm_fvar uu____19935) ->
                   let head1 =
                     let uu____19939 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____19939
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____19983 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____19983
                       FStar_Pervasives_Native.fst in
                   let uu____20024 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20024
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20039 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20039
                      then
                        let guard =
                          let uu____20051 =
                            let uu____20052 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20052 = FStar_Syntax_Util.Equal in
                          if uu____20051
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20056 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_88  ->
                                  FStar_Pervasives_Native.Some _0_88)
                               uu____20056) in
                        let uu____20059 = solve_prob orig guard [] wl in
                        solve env uu____20059
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20062,FStar_Syntax_Syntax.Tm_app uu____20063) ->
                   let head1 =
                     let uu____20081 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right uu____20081
                       FStar_Pervasives_Native.fst in
                   let head2 =
                     let uu____20125 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right uu____20125
                       FStar_Pervasives_Native.fst in
                   let uu____20166 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____20166
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____20181 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____20181
                      then
                        let guard =
                          let uu____20193 =
                            let uu____20194 = FStar_Syntax_Util.eq_tm t1 t2 in
                            uu____20194 = FStar_Syntax_Util.Equal in
                          if uu____20193
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20198 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_Pervasives_Native.Some _0_89)
                               uu____20198) in
                        let uu____20201 = solve_prob orig guard [] wl in
                        solve env uu____20201
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let uu____20204,uu____20205) ->
                   let uu____20218 =
                     let uu____20219 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20220 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20219
                       uu____20220 in
                   failwith uu____20218
               | (FStar_Syntax_Syntax.Tm_delayed uu____20221,uu____20222) ->
                   let uu____20247 =
                     let uu____20248 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20249 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20248
                       uu____20249 in
                   failwith uu____20247
               | (uu____20250,FStar_Syntax_Syntax.Tm_delayed uu____20251) ->
                   let uu____20276 =
                     let uu____20277 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20278 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20277
                       uu____20278 in
                   failwith uu____20276
               | (uu____20279,FStar_Syntax_Syntax.Tm_let uu____20280) ->
                   let uu____20293 =
                     let uu____20294 = FStar_Syntax_Print.tag_of_term t1 in
                     let uu____20295 = FStar_Syntax_Print.tag_of_term t2 in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20294
                       uu____20295 in
                   failwith uu____20293
               | uu____20296 -> giveup env "head tag mismatch" orig)))
and (solve_c
  :FStar_TypeChecker_Env.env ->
     (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
       -> worklist -> solution)=
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
          (let uu____20332 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____20332
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____20334 =
               let uu____20335 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name in
               let uu____20336 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20335 uu____20336 in
             giveup env uu____20334 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____20356  ->
                    fun uu____20357  ->
                      match (uu____20356, uu____20357) with
                      | ((a1,uu____20375),(a2,uu____20377)) ->
                          let uu____20386 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg" in
                          FStar_All.pipe_left
                            (fun _0_90  ->
                               FStar_TypeChecker_Common.TProb _0_90)
                            uu____20386)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args in
             let guard =
               let uu____20396 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs in
               FStar_Syntax_Util.mk_conj_l uu____20396 in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl in
             solve env (attempt sub_probs wl1)) in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env in
          let lift_c1 uu____20420 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20427)::[] -> wp1
              | uu____20444 ->
                  let uu____20453 =
                    let uu____20454 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name) in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20454 in
                  failwith uu____20453 in
            let uu____20457 =
              let uu____20466 =
                let uu____20467 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp in
                FStar_Syntax_Syntax.as_arg uu____20467 in
              [uu____20466] in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20457;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            } in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20468 = lift_c1 () in solve_eq uu____20468 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___138_20474  ->
                       match uu___138_20474 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20475 -> false)) in
             let uu____20476 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20510)::uu____20511,(wp2,uu____20513)::uu____20514)
                   -> (wp1, wp2)
               | uu____20571 ->
                   let uu____20592 =
                     let uu____20593 =
                       let uu____20598 =
                         let uu____20599 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name in
                         let uu____20600 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____20599 uu____20600 in
                       (uu____20598, (env.FStar_TypeChecker_Env.range)) in
                     FStar_Errors.Error uu____20593 in
                   FStar_Exn.raise uu____20592 in
             match uu____20476 with
             | (wpc1,wpc2) ->
                 let uu____20619 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____20619
                 then
                   let uu____20622 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type" in
                   solve_t env uu____20622 wl
                 else
                   (let uu____20626 =
                      let uu____20633 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.must uu____20633 in
                    match uu____20626 with
                    | (c2_decl,qualifiers) ->
                        let uu____20654 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable) in
                        if uu____20654
                        then
                          let c1_repr =
                            let uu____20658 =
                              let uu____20659 =
                                let uu____20660 = lift_c1 () in
                                FStar_Syntax_Syntax.mk_Comp uu____20660 in
                              let uu____20661 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20659 uu____20661 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____20658 in
                          let c2_repr =
                            let uu____20663 =
                              let uu____20664 =
                                FStar_Syntax_Syntax.mk_Comp c21 in
                              let uu____20665 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20664 uu____20665 in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____20663 in
                          let prob =
                            let uu____20667 =
                              let uu____20672 =
                                let uu____20673 =
                                  FStar_Syntax_Print.term_to_string c1_repr in
                                let uu____20674 =
                                  FStar_Syntax_Print.term_to_string c2_repr in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____20673
                                  uu____20674 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____20672 in
                            FStar_TypeChecker_Common.TProb uu____20667 in
                          let wl1 =
                            let uu____20676 =
                              let uu____20679 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst in
                              FStar_Pervasives_Native.Some uu____20679 in
                            solve_prob orig uu____20676 [] wl in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____20688 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel") in
                                   if uu____20688
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____20690 =
                                     let uu____20693 =
                                       let uu____20694 =
                                         let uu____20709 =
                                           let uu____20710 =
                                             let uu____20711 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ in
                                             [uu____20711] in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____20710 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial in
                                         let uu____20712 =
                                           let uu____20715 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           let uu____20716 =
                                             let uu____20719 =
                                               let uu____20720 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1 in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20720 in
                                             [uu____20719] in
                                           uu____20715 :: uu____20716 in
                                         (uu____20709, uu____20712) in
                                       FStar_Syntax_Syntax.Tm_app uu____20694 in
                                     FStar_Syntax_Syntax.mk uu____20693 in
                                   uu____20690 FStar_Pervasives_Native.None r))
                               else
                                 (let uu____20727 =
                                    let uu____20730 =
                                      let uu____20731 =
                                        let uu____20746 =
                                          let uu____20747 =
                                            let uu____20748 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ in
                                            [uu____20748] in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____20747 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger in
                                        let uu____20749 =
                                          let uu____20752 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____20753 =
                                            let uu____20756 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            let uu____20757 =
                                              let uu____20760 =
                                                let uu____20761 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1 in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20761 in
                                              [uu____20760] in
                                            uu____20756 :: uu____20757 in
                                          uu____20752 :: uu____20753 in
                                        (uu____20746, uu____20749) in
                                      FStar_Syntax_Syntax.Tm_app uu____20731 in
                                    FStar_Syntax_Syntax.mk uu____20730 in
                                  uu____20727 FStar_Pervasives_Native.None r) in
                           let base_prob =
                             let uu____20768 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             FStar_All.pipe_left
                               (fun _0_91  ->
                                  FStar_TypeChecker_Common.TProb _0_91)
                               uu____20768 in
                           let wl1 =
                             let uu____20778 =
                               let uu____20781 =
                                 let uu____20784 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst in
                                 FStar_Syntax_Util.mk_conj uu____20784 g in
                               FStar_All.pipe_left
                                 (fun _0_92  ->
                                    FStar_Pervasives_Native.Some _0_92)
                                 uu____20781 in
                             solve_prob orig uu____20778 [] wl in
                           solve env (attempt [base_prob] wl1)))) in
        let uu____20797 = FStar_Util.physical_equality c1 c2 in
        if uu____20797
        then
          let uu____20798 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____20798
        else
          ((let uu____20801 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____20801
            then
              let uu____20802 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____20803 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____20802
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____20803
            else ());
           (let uu____20805 =
              let uu____20810 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____20811 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____20810, uu____20811) in
            match uu____20805 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20815),FStar_Syntax_Syntax.Total
                    (t2,uu____20817)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____20834 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20834 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20837,FStar_Syntax_Syntax.Total uu____20838) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20856),FStar_Syntax_Syntax.Total
                    (t2,uu____20858)) ->
                     let uu____20875 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20875 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20879),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20881)) ->
                     let uu____20898 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20898 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20902),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20904)) ->
                     let uu____20921 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____20921 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20924,FStar_Syntax_Syntax.Comp uu____20925) ->
                     let uu____20934 =
                       let uu___183_20939 = problem in
                       let uu____20944 =
                         let uu____20945 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20945 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___183_20939.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20944;
                         FStar_TypeChecker_Common.relation =
                           (uu___183_20939.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___183_20939.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___183_20939.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___183_20939.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___183_20939.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___183_20939.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___183_20939.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___183_20939.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20934 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____20946,FStar_Syntax_Syntax.Comp uu____20947) ->
                     let uu____20956 =
                       let uu___183_20961 = problem in
                       let uu____20966 =
                         let uu____20967 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20967 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___183_20961.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20966;
                         FStar_TypeChecker_Common.relation =
                           (uu___183_20961.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___183_20961.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___183_20961.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___183_20961.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___183_20961.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___183_20961.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___183_20961.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___183_20961.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20956 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20968,FStar_Syntax_Syntax.GTotal uu____20969) ->
                     let uu____20978 =
                       let uu___184_20983 = problem in
                       let uu____20988 =
                         let uu____20989 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20989 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___184_20983.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___184_20983.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___184_20983.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20988;
                         FStar_TypeChecker_Common.element =
                           (uu___184_20983.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___184_20983.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___184_20983.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___184_20983.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___184_20983.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___184_20983.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____20978 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20990,FStar_Syntax_Syntax.Total uu____20991) ->
                     let uu____21000 =
                       let uu___184_21005 = problem in
                       let uu____21010 =
                         let uu____21011 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21011 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___184_21005.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___184_21005.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___184_21005.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21010;
                         FStar_TypeChecker_Common.element =
                           (uu___184_21005.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___184_21005.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___184_21005.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___184_21005.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___184_21005.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___184_21005.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____21000 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21012,FStar_Syntax_Syntax.Comp uu____21013) ->
                     let uu____21014 =
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
                     if uu____21014
                     then
                       let uu____21015 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____21015 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21021 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21031 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____21032 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____21031, uu____21032)) in
                          match uu____21021 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu____21039 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____21039
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21041 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name in
                            match uu____21041 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21044 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____21046 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ in
                                     FStar_Syntax_Util.non_informative
                                       uu____21046) in
                                if uu____21044
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
                                  (let uu____21049 =
                                     let uu____21050 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name in
                                     let uu____21051 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____21050 uu____21051 in
                                   giveup env uu____21049 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))
let (print_pending_implicits :FStar_TypeChecker_Env.guard_t -> Prims.string)=
  fun g  ->
    let uu____21057 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21095  ->
              match uu____21095 with
              | (uu____21108,uu____21109,u,uu____21111,uu____21112,uu____21113)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right uu____21057 (FStar_String.concat ", ")
let (ineqs_to_string
  :(FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                              FStar_Syntax_Syntax.universe)
                                              FStar_Pervasives_Native.tuple2
                                              Prims.list)
     FStar_Pervasives_Native.tuple2 -> Prims.string)=
  fun ineqs  ->
    let vars =
      let uu____21145 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____21145 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____21163 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21191  ->
                match uu____21191 with
                | (u1,u2) ->
                    let uu____21198 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____21199 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____21198 uu____21199)) in
      FStar_All.pipe_right uu____21163 (FStar_String.concat ", ") in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1
let (guard_to_string
  :FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.string)=
  fun env  ->
    fun g  ->
      match ((g.FStar_TypeChecker_Env.guard_f),
              (g.FStar_TypeChecker_Env.deferred),
              (g.FStar_TypeChecker_Env.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21218,[])) -> "{}"
      | uu____21243 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21260 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____21260
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let uu____21263 =
              FStar_List.map
                (fun uu____21273  ->
                   match uu____21273 with
                   | (uu____21278,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right uu____21263 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____21283 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21283 imps
let new_t_problem :
  'Auu____21298 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21298 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21298)
                  FStar_TypeChecker_Common.problem=
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21332 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel") in
                if uu____21332
                then
                  let uu____21333 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs in
                  let uu____21334 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21333
                    (rel_to_string rel) uu____21334
                else "TOP" in
              let p = new_problem env lhs rel rhs elt loc reason in p
let (new_t_prob
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.typ ->
       FStar_TypeChecker_Common.rel ->
         FStar_Syntax_Syntax.term ->
           (FStar_TypeChecker_Common.prob,FStar_Syntax_Syntax.bv)
             FStar_Pervasives_Native.tuple2)=
  fun env  ->
    fun t1  ->
      fun rel  ->
        fun t2  ->
          let x =
            let uu____21362 =
              let uu____21365 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left
                (fun _0_93  -> FStar_Pervasives_Native.Some _0_93)
                uu____21365 in
            FStar_Syntax_Syntax.new_bv uu____21362 t1 in
          let env1 = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let uu____21374 =
              let uu____21377 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left
                (fun _0_94  -> FStar_Pervasives_Native.Some _0_94)
                uu____21377 in
            let uu____21380 = FStar_TypeChecker_Env.get_range env1 in
            new_t_problem env1 t1 rel t2 uu____21374 uu____21380 in
          ((FStar_TypeChecker_Common.TProb p), x)
let (solve_and_commit
  :FStar_TypeChecker_Env.env ->
     worklist ->
       ((FStar_TypeChecker_Common.prob,Prims.string)
          FStar_Pervasives_Native.tuple2 ->
          FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option)
         -> FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option)=
  fun env  ->
    fun probs  ->
      fun err1  ->
        let probs1 =
          let uu____21413 = FStar_Options.eager_inference () in
          if uu____21413
          then
            let uu___185_21414 = probs in
            {
              attempting = (uu___185_21414.attempting);
              wl_deferred = (uu___185_21414.wl_deferred);
              ctr = (uu___185_21414.ctr);
              defer_ok = false;
              smt_ok = (uu___185_21414.smt_ok);
              tcenv = (uu___185_21414.tcenv)
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
             (let uu____21426 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____21426
              then
                let uu____21427 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string uu____21427
              else ());
             err1 (d, s))
let (simplify_guard
  :FStar_TypeChecker_Env.env ->
     FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)=
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____21439 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____21439
            then
              let uu____21440 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21440
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops] env f in
            (let uu____21444 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____21444
             then
               let uu____21445 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21445
             else ());
            (let f2 =
               let uu____21448 =
                 let uu____21449 = FStar_Syntax_Util.unmeta f1 in
                 uu____21449.FStar_Syntax_Syntax.n in
               match uu____21448 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21453 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___186_21454 = g in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___186_21454.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___186_21454.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___186_21454.FStar_TypeChecker_Env.implicits)
             })))
let (with_guard
  :FStar_TypeChecker_Env.env ->
     FStar_TypeChecker_Common.prob ->
       FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option ->
         FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)=
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some d ->
            let uu____21476 =
              let uu____21477 =
                let uu____21478 =
                  let uu____21479 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst in
                  FStar_All.pipe_right uu____21479
                    (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95) in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21478;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env uu____21477 in
            FStar_All.pipe_left
              (fun _0_96  -> FStar_Pervasives_Native.Some _0_96) uu____21476
let with_guard_no_simp :
  'Auu____21510 .
    'Auu____21510 ->
      FStar_TypeChecker_Common.prob ->
        FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option=
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some d ->
            let uu____21530 =
              let uu____21531 =
                let uu____21532 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____21532
                  (fun _0_97  -> FStar_TypeChecker_Common.NonTrivial _0_97) in
              {
                FStar_TypeChecker_Env.guard_f = uu____21531;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              } in
            FStar_Pervasives_Native.Some uu____21530
let (try_teq
  :Prims.bool ->
     FStar_TypeChecker_Env.env ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.typ ->
           FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)=
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____21574 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21574
           then
             let uu____21575 = FStar_Syntax_Print.term_to_string t1 in
             let uu____21576 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21575
               uu____21576
           else ());
          (let prob =
             let uu____21579 =
               let uu____21584 = FStar_TypeChecker_Env.get_range env in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____21584 in
             FStar_All.pipe_left
               (fun _0_98  -> FStar_TypeChecker_Common.TProb _0_98)
               uu____21579 in
           let g =
             let uu____21592 =
               let uu____21595 = singleton' env prob smt_ok in
               solve_and_commit env uu____21595
                 (fun uu____21597  -> FStar_Pervasives_Native.None) in
             FStar_All.pipe_left (with_guard env prob) uu____21592 in
           g)
let (teq
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.typ ->
       FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)=
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21618 = try_teq true env t1 t2 in
        match uu____21618 with
        | FStar_Pervasives_Native.None  ->
            let uu____21621 =
              let uu____21622 =
                let uu____21627 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1 in
                let uu____21628 = FStar_TypeChecker_Env.get_range env in
                (uu____21627, uu____21628) in
              FStar_Errors.Error uu____21622 in
            FStar_Exn.raise uu____21621
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21631 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____21631
              then
                let uu____21632 = FStar_Syntax_Print.term_to_string t1 in
                let uu____21633 = FStar_Syntax_Print.term_to_string t2 in
                let uu____21634 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21632
                  uu____21633 uu____21634
              else ());
             g)
let (try_subtype'
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.typ ->
       FStar_Syntax_Syntax.typ ->
         Prims.bool ->
           FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)=
  fun env  ->
    fun t1  ->
      fun t2  ->
        fun smt_ok  ->
          (let uu____21655 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____21655
           then
             let uu____21656 =
               FStar_TypeChecker_Normalize.term_to_string env t1 in
             let uu____21657 =
               FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____21656
               uu____21657
           else ());
          (let uu____21659 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____21659 with
           | (prob,x) ->
               let g =
                 let uu____21671 =
                   let uu____21674 = singleton' env prob smt_ok in
                   solve_and_commit env uu____21674
                     (fun uu____21676  -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____21671 in
               ((let uu____21686 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____21686
                 then
                   let uu____21687 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let uu____21688 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let uu____21689 =
                     let uu____21690 = FStar_Util.must g in
                     guard_to_string env uu____21690 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____21687 uu____21688 uu____21689
                 else ());
                abstract_guard x g))
let (try_subtype
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.typ ->
       FStar_Syntax_Syntax.typ ->
         FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)=
  fun env  -> fun t1  -> fun t2  -> try_subtype' env t1 t2 true
let (subtype_fail
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.term ->
       FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.unit)=
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____21722 = FStar_TypeChecker_Env.get_range env in
          let uu____21723 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.err uu____21722 uu____21723
let (sub_comp
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.comp ->
       FStar_Syntax_Syntax.comp ->
         FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)=
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____21739 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____21739
         then
           let uu____21740 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____21741 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____21740
             uu____21741
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let uu____21746 =
             let uu____21751 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____21751 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_99  -> FStar_TypeChecker_Common.CProb _0_99) uu____21746 in
         let uu____21756 =
           let uu____21759 = singleton env prob in
           solve_and_commit env uu____21759
             (fun uu____21761  -> FStar_Pervasives_Native.None) in
         FStar_All.pipe_left (with_guard env prob) uu____21756)
let (solve_universe_inequalities'
  :FStar_Syntax_Unionfind.tx ->
     FStar_TypeChecker_Env.env ->
       (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                                  FStar_Syntax_Syntax.universe)
                                                  FStar_Pervasives_Native.tuple2
                                                  Prims.list)
         FStar_Pervasives_Native.tuple2 -> Prims.unit)=
  fun tx  ->
    fun env  ->
      fun uu____21793  ->
        match uu____21793 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____21832 =
                 let uu____21833 =
                   let uu____21838 =
                     let uu____21839 = FStar_Syntax_Print.univ_to_string u1 in
                     let uu____21840 = FStar_Syntax_Print.univ_to_string u2 in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____21839 uu____21840 in
                   let uu____21841 = FStar_TypeChecker_Env.get_range env in
                   (uu____21838, uu____21841) in
                 FStar_Errors.Error uu____21833 in
               FStar_Exn.raise uu____21832) in
            let equiv1 v1 v' =
              let uu____21849 =
                let uu____21854 = FStar_Syntax_Subst.compress_univ v1 in
                let uu____21855 = FStar_Syntax_Subst.compress_univ v' in
                (uu____21854, uu____21855) in
              match uu____21849 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____21874 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____21904 = FStar_Syntax_Subst.compress_univ v1 in
                      match uu____21904 with
                      | FStar_Syntax_Syntax.U_unif uu____21911 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____21940  ->
                                    match uu____21940 with
                                    | (u,v') ->
                                        let uu____21949 = equiv1 v1 v' in
                                        if uu____21949
                                        then
                                          let uu____21952 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u)) in
                                          (if uu____21952 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v1)]
                      | uu____21968 -> [])) in
            let uu____21973 =
              let wl =
                let uu___187_21977 = empty_worklist env in
                {
                  attempting = (uu___187_21977.attempting);
                  wl_deferred = (uu___187_21977.wl_deferred);
                  ctr = (uu___187_21977.ctr);
                  defer_ok = false;
                  smt_ok = (uu___187_21977.smt_ok);
                  tcenv = (uu___187_21977.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____21995  ->
                      match uu____21995 with
                      | (lb,v1) ->
                          let uu____22002 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v1 in
                          (match uu____22002 with
                           | USolved wl1 -> ()
                           | uu____22004 -> fail lb v1))) in
            let rec check_ineq uu____22012 =
              match uu____22012 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1 in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22021) -> true
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
                      uu____22044,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22046,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22057) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22064,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22072 -> false) in
            let uu____22077 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22092  ->
                      match uu____22092 with
                      | (u,v1) ->
                          let uu____22099 = check_ineq (u, v1) in
                          if uu____22099
                          then true
                          else
                            ((let uu____22102 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____22102
                              then
                                let uu____22103 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____22104 =
                                  FStar_Syntax_Print.univ_to_string v1 in
                                FStar_Util.print2 "%s </= %s" uu____22103
                                  uu____22104
                              else ());
                             false))) in
            if uu____22077
            then ()
            else
              ((let uu____22108 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____22108
                then
                  ((let uu____22110 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22110);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22120 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22120))
                else ());
               (let uu____22130 =
                  let uu____22131 =
                    let uu____22136 = FStar_TypeChecker_Env.get_range env in
                    ("Failed to solve universe inequalities for inductives",
                      uu____22136) in
                  FStar_Errors.Error uu____22131 in
                FStar_Exn.raise uu____22130))
let (solve_universe_inequalities
  :FStar_TypeChecker_Env.env ->
     (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                                FStar_Syntax_Syntax.universe)
                                                FStar_Pervasives_Native.tuple2
                                                Prims.list)
       FStar_Pervasives_Native.tuple2 -> Prims.unit)=
  fun env  ->
    fun ineqs  ->
      let tx = FStar_Syntax_Unionfind.new_transaction () in
      solve_universe_inequalities' tx env ineqs;
      FStar_Syntax_Unionfind.commit tx
let rec (solve_deferred_constraints
  :FStar_TypeChecker_Env.env ->
     FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)=
  fun env  ->
    fun g  ->
      let fail uu____22188 =
        match uu____22188 with
        | (d,s) ->
            let msg = explain env d s in
            FStar_Exn.raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____22202 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____22202
       then
         let uu____22203 = wl_to_string wl in
         let uu____22204 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22203 uu____22204
       else ());
      (let g1 =
         let uu____22219 = solve_and_commit env wl fail in
         match uu____22219 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___188_22232 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___188_22232.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___188_22232.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___188_22232.FStar_TypeChecker_Env.implicits)
             }
         | uu____22237 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___189_22241 = g1 in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___189_22241.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___189_22241.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___189_22241.FStar_TypeChecker_Env.implicits)
        }))
let (last_proof_ns
  :FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
     FStar_ST.ref)=
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let (maybe_update_proof_ns :FStar_TypeChecker_Env.env -> Prims.unit)=
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns in
    let uu____22264 = FStar_ST.op_Bang last_proof_ns in
    match uu____22264 with
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
let (discharge_guard'
  :(Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
     FStar_TypeChecker_Env.env ->
       FStar_TypeChecker_Env.guard_t ->
         Prims.bool ->
           FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)=
  fun use_env_range_msg  ->
    fun env  ->
      fun g  ->
        fun use_smt  ->
          let g1 = solve_deferred_constraints env g in
          let ret_g =
            let uu___190_22355 = g1 in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___190_22355.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___190_22355.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___190_22355.FStar_TypeChecker_Env.implicits)
            } in
          let uu____22356 =
            let uu____22357 = FStar_TypeChecker_Env.should_verify env in
            Prims.op_Negation uu____22357 in
          if uu____22356
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____22365 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery")) in
                   if uu____22365
                   then
                     let uu____22366 = FStar_TypeChecker_Env.get_range env in
                     let uu____22367 =
                       let uu____22368 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22368 in
                     FStar_Errors.diag uu____22366 uu____22367
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc in
                   let uu____22371 = check_trivial vc1 in
                   match uu____22371 with
                   | FStar_TypeChecker_Common.Trivial  ->
                       FStar_Pervasives_Native.Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then
                         ((let uu____22378 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____22378
                           then
                             let uu____22379 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____22380 =
                               let uu____22381 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1
                                 "Cannot solve without SMT : %s\n"
                                 uu____22381 in
                             FStar_Errors.diag uu____22379 uu____22380
                           else ());
                          FStar_Pervasives_Native.None)
                       else
                         ((let uu____22386 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____22386
                           then
                             let uu____22387 =
                               FStar_TypeChecker_Env.get_range env in
                             let uu____22388 =
                               let uu____22389 =
                                 FStar_Syntax_Print.term_to_string vc2 in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____22389 in
                             FStar_Errors.diag uu____22387 uu____22388
                           else ());
                          (let vcs =
                             let uu____22400 = FStar_Options.use_tactics () in
                             if uu____22400
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else
                               (let uu____22410 =
                                  let uu____22417 = FStar_Options.peek () in
                                  (env, vc2, uu____22417) in
                                [uu____22410]) in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____22451  ->
                                   match uu____22451 with
                                   | (env1,goal,opts) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify;
                                           FStar_TypeChecker_Normalize.Primops]
                                           env1 goal in
                                       let uu____22462 = check_trivial goal1 in
                                       (match uu____22462 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____22464 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac")) in
                                            if uu____22464
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            (FStar_Options.push ();
                                             FStar_Options.set opts;
                                             maybe_update_proof_ns env1;
                                             (let uu____22471 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel") in
                                              if uu____22471
                                              then
                                                let uu____22472 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1 in
                                                let uu____22473 =
                                                  let uu____22474 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2 in
                                                  let uu____22475 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1 in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____22474 uu____22475 in
                                                FStar_Errors.diag uu____22472
                                                  uu____22473
                                              else ());
                                             (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                               use_env_range_msg env1 goal2;
                                             FStar_Options.pop ())))));
                          FStar_Pervasives_Native.Some ret_g))))
let (discharge_guard_no_smt
  :FStar_TypeChecker_Env.env ->
     FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)=
  fun env  ->
    fun g  ->
      let uu____22487 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____22487 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22493 =
            let uu____22494 =
              let uu____22499 = FStar_TypeChecker_Env.get_range env in
              ("Expected a trivial pre-condition", uu____22499) in
            FStar_Errors.Error uu____22494 in
          FStar_Exn.raise uu____22493
let (discharge_guard
  :FStar_TypeChecker_Env.env ->
     FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)=
  fun env  ->
    fun g  ->
      let uu____22508 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____22508 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let (resolve_implicits'
  :Prims.bool ->
     FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)=
  fun forcelax  ->
    fun g  ->
      let unresolved u =
        let uu____22526 = FStar_Syntax_Unionfind.find u in
        match uu____22526 with
        | FStar_Pervasives_Native.None  -> true
        | uu____22529 -> false in
      let rec until_fixpoint acc implicits =
        let uu____22547 = acc in
        match uu____22547 with
        | (out,changed) ->
            (match implicits with
             | [] ->
                 if Prims.op_Negation changed
                 then out
                 else until_fixpoint ([], false) out
             | hd1::tl1 ->
                 let uu____22633 = hd1 in
                 (match uu____22633 with
                  | (uu____22646,env,u,tm,k,r) ->
                      let uu____22652 = unresolved u in
                      if uu____22652
                      then until_fixpoint ((hd1 :: out), changed) tl1
                      else
                        (let env1 =
                           FStar_TypeChecker_Env.set_expected_typ env k in
                         let tm1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta] env1 tm in
                         (let uu____22683 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "RelCheck") in
                          if uu____22683
                          then
                            let uu____22684 =
                              FStar_Syntax_Print.uvar_to_string u in
                            let uu____22685 =
                              FStar_Syntax_Print.term_to_string tm1 in
                            let uu____22686 =
                              FStar_Syntax_Print.term_to_string k in
                            FStar_Util.print3
                              "Checking uvar %s resolved to %s at type %s\n"
                              uu____22684 uu____22685 uu____22686
                          else ());
                         (let env2 =
                            if forcelax
                            then
                              let uu___191_22689 = env1 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___191_22689.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___191_22689.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___191_22689.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___191_22689.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___191_22689.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___191_22689.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___191_22689.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___191_22689.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___191_22689.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___191_22689.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___191_22689.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___191_22689.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___191_22689.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___191_22689.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___191_22689.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___191_22689.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___191_22689.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___191_22689.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___191_22689.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.failhard =
                                  (uu___191_22689.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___191_22689.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___191_22689.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___191_22689.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___191_22689.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___191_22689.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___191_22689.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___191_22689.FStar_TypeChecker_Env.is_native_tactic);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___191_22689.FStar_TypeChecker_Env.identifier_info)
                              }
                            else env1 in
                          let uu____22691 =
                            env2.FStar_TypeChecker_Env.type_of
                              (let uu___192_22699 = env2 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___192_22699.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___192_22699.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___192_22699.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___192_22699.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___192_22699.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___192_22699.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___192_22699.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___192_22699.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___192_22699.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___192_22699.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___192_22699.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___192_22699.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___192_22699.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___192_22699.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___192_22699.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___192_22699.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___192_22699.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___192_22699.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___192_22699.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___192_22699.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___192_22699.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___192_22699.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___192_22699.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___192_22699.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___192_22699.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___192_22699.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___192_22699.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___192_22699.FStar_TypeChecker_Env.identifier_info)
                               }) tm1 in
                          match uu____22691 with
                          | (uu____22700,uu____22701,g1) ->
                              let g2 =
                                if env2.FStar_TypeChecker_Env.is_pattern
                                then
                                  let uu___193_22704 = g1 in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      FStar_TypeChecker_Common.Trivial;
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___193_22704.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___193_22704.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits =
                                      (uu___193_22704.FStar_TypeChecker_Env.implicits)
                                  }
                                else g1 in
                              let g' =
                                let uu____22707 =
                                  discharge_guard'
                                    (FStar_Pervasives_Native.Some
                                       (fun uu____22713  ->
                                          FStar_Syntax_Print.term_to_string
                                            tm1)) env2 g2 true in
                                match uu____22707 with
                                | FStar_Pervasives_Native.Some g3 -> g3
                                | FStar_Pervasives_Native.None  ->
                                    failwith
                                      "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                              until_fixpoint
                                ((FStar_List.append
                                    g'.FStar_TypeChecker_Env.implicits out),
                                  true) tl1)))) in
      let uu___194_22741 = g in
      let uu____22742 =
        until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___194_22741.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___194_22741.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs =
          (uu___194_22741.FStar_TypeChecker_Env.univ_ineqs);
        FStar_TypeChecker_Env.implicits = uu____22742
      }
let (resolve_implicits
  :FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)=
  fun g  -> resolve_implicits' false g
let (resolve_implicits_lax
  :FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)=
  fun g  -> resolve_implicits' true g
let (force_trivial_guard
  :FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit)=
  fun env  ->
    fun g  ->
      let g1 =
        let uu____22800 = solve_deferred_constraints env g in
        FStar_All.pipe_right uu____22800 resolve_implicits in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____22813 = discharge_guard env g1 in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____22813
      | (reason,uu____22815,uu____22816,e,t,r)::uu____22820 ->
          let uu____22847 =
            let uu____22848 =
              let uu____22853 =
                let uu____22854 = FStar_Syntax_Print.term_to_string t in
                let uu____22855 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format2
                  "Failed to resolve implicit argument of type '%s' introduced in %s"
                  uu____22854 uu____22855 in
              (uu____22853, r) in
            FStar_Errors.Error uu____22848 in
          FStar_Exn.raise uu____22847
let (universe_inequality
  :FStar_Syntax_Syntax.universe ->
     FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)=
  fun u1  ->
    fun u2  ->
      let uu___195_22864 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___195_22864.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___195_22864.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___195_22864.FStar_TypeChecker_Env.implicits)
      }
let (teq_nosmt
  :FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)=
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22893 = try_teq false env t1 t2 in
        match uu____22893 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g ->
            let uu____22897 =
              discharge_guard' FStar_Pervasives_Native.None env g false in
            (match uu____22897 with
             | FStar_Pervasives_Native.Some uu____22902 -> true
             | FStar_Pervasives_Native.None  -> false)