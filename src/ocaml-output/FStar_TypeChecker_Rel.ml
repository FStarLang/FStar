open Prims
let (guard_of_guard_formula :
  FStar_TypeChecker_Common.guard_formula -> FStar_TypeChecker_Env.guard_t) =
  fun g  ->
    {
      FStar_TypeChecker_Env.guard_f = g;
      FStar_TypeChecker_Env.deferred = [];
      FStar_TypeChecker_Env.univ_ineqs = ([], []);
      FStar_TypeChecker_Env.implicits = []
    }
  
let (guard_form :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun g  -> g.FStar_TypeChecker_Env.guard_f 
let (is_trivial : FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Env.deferred = [];
        FStar_TypeChecker_Env.univ_ineqs = uu____30;
        FStar_TypeChecker_Env.implicits = uu____31;_} -> true
    | uu____58 -> false
  
let (trivial_guard : FStar_TypeChecker_Env.guard_t) =
  {
    FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial;
    FStar_TypeChecker_Env.deferred = [];
    FStar_TypeChecker_Env.univ_ineqs = ([], []);
    FStar_TypeChecker_Env.implicits = []
  } 
let (abstract_guard_n :
  FStar_Syntax_Syntax.binder Prims.list ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun bs  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let f' =
            FStar_Syntax_Util.abs bs f
              (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
             in
          let uu___113_91 = g  in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___113_91.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___113_91.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___113_91.FStar_TypeChecker_Env.implicits)
          }
  
let (abstract_guard :
  FStar_Syntax_Syntax.binder ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun b  -> fun g  -> abstract_guard_n [b] g 
let (guard_unbound_vars :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          FStar_Util.new_set FStar_Syntax_Syntax.order_bv
      | FStar_TypeChecker_Common.NonTrivial f ->
          FStar_TypeChecker_Env.unbound_vars env f
  
let (check_guard :
  Prims.string ->
    FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit)
  =
  fun msg  ->
    fun env  ->
      fun g  ->
        let s = guard_unbound_vars env g  in
        let uu____121 = FStar_Util.set_is_empty s  in
        if uu____121
        then ()
        else
          (let uu____123 =
             let uu____128 =
               let uu____129 =
                 let uu____130 =
                   let uu____133 = FStar_Util.set_elements s  in
                   FStar_All.pipe_right uu____133
                     (FStar_List.map FStar_Syntax_Syntax.mk_binder)
                    in
                 FStar_All.pipe_right uu____130
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               FStar_Util.format2 "Guard has free variables (%s): %s" msg
                 uu____129
                in
             (FStar_Errors.Fatal_FreeVariables, uu____128)  in
           FStar_Errors.raise_err uu____123)
  
let (check_term :
  Prims.string ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun msg  ->
    fun env  ->
      fun t  ->
        let s = FStar_TypeChecker_Env.unbound_vars env t  in
        let uu____154 = FStar_Util.set_is_empty s  in
        if uu____154
        then ()
        else
          (let uu____156 =
             let uu____161 =
               let uu____162 = FStar_Syntax_Print.term_to_string t  in
               let uu____163 =
                 let uu____164 =
                   let uu____167 = FStar_Util.set_elements s  in
                   FStar_All.pipe_right uu____167
                     (FStar_List.map FStar_Syntax_Syntax.mk_binder)
                    in
                 FStar_All.pipe_right uu____164
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               FStar_Util.format3 "Term <%s> has free variables (%s): %s"
                 uu____162 msg uu____163
                in
             (FStar_Errors.Fatal_FreeVariables, uu____161)  in
           FStar_Errors.raise_err uu____156)
  
let (apply_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t)
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___114_183 = g  in
          let uu____184 =
            let uu____185 =
              let uu____186 =
                let uu____189 =
                  let uu____190 =
                    let uu____205 =
                      let uu____208 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____208]  in
                    (f, uu____205)  in
                  FStar_Syntax_Syntax.Tm_app uu____190  in
                FStar_Syntax_Syntax.mk uu____189  in
              uu____186 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_40  -> FStar_TypeChecker_Common.NonTrivial _0_40)
              uu____185
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____184;
            FStar_TypeChecker_Env.deferred =
              (uu___114_183.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___114_183.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___114_183.FStar_TypeChecker_Env.implicits)
          }
  
let (map_guard :
  FStar_TypeChecker_Env.guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      FStar_TypeChecker_Env.guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___115_226 = g  in
          let uu____227 =
            let uu____228 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____228  in
          {
            FStar_TypeChecker_Env.guard_f = uu____227;
            FStar_TypeChecker_Env.deferred =
              (uu___115_226.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___115_226.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___115_226.FStar_TypeChecker_Env.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> Prims.unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____232 -> failwith "impossible"
  
let (conj_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) -> g
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let uu____243 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____243
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____247 =
      let uu____248 = FStar_Syntax_Util.unmeta t  in
      uu____248.FStar_Syntax_Syntax.n  in
    match uu____247 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____252 -> FStar_TypeChecker_Common.NonTrivial t
  
let (imp_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) ->
          FStar_TypeChecker_Common.Trivial
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let imp = FStar_Syntax_Util.mk_imp f1 f2  in check_trivial imp
  
let (binop_guard :
  (FStar_TypeChecker_Common.guard_formula ->
     FStar_TypeChecker_Common.guard_formula ->
       FStar_TypeChecker_Common.guard_formula)
    ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun f  ->
    fun g1  ->
      fun g2  ->
        let uu____283 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f
           in
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
  
let (conj_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun g1  -> fun g2  -> binop_guard conj_guard_f g1 g2 
let (imp_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun g1  -> fun g2  -> binop_guard imp_guard_f g1 g2 
let (close_guard_univs :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
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
                       let uu____350 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____350
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___116_352 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___116_352.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___116_352.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___116_352.FStar_TypeChecker_Env.implicits)
            }
  
let (close_forall :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binder Prims.list ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun bs  ->
      fun f  ->
        FStar_List.fold_right
          (fun b  ->
             fun f1  ->
               let uu____371 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____371
               then f1
               else
                 (let u =
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  FStar_Syntax_Util.mk_forall u
                    (FStar_Pervasives_Native.fst b) f1)) bs f
  
let (close_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun binders  ->
      fun g  ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___117_384 = g  in
            let uu____385 =
              let uu____386 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____386  in
            {
              FStar_TypeChecker_Env.guard_f = uu____385;
              FStar_TypeChecker_Env.deferred =
                (uu___117_384.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___117_384.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___117_384.FStar_TypeChecker_Env.implicits)
            }
  
let (new_uvar :
  FStar_Range.range ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
          FStar_Pervasives_Native.tuple2)
  =
  fun r  ->
    fun binders  ->
      fun k  ->
        let uv = FStar_Syntax_Unionfind.fresh ()  in
        match binders with
        | [] ->
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k))
                FStar_Pervasives_Native.None r
               in
            (uv1, uv1)
        | uu____416 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder)
               in
            let k' =
              let uu____441 = FStar_Syntax_Syntax.mk_Total k  in
              FStar_Syntax_Util.arrow binders uu____441  in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                FStar_Pervasives_Native.None r
               in
            let uu____449 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                FStar_Pervasives_Native.None r
               in
            (uu____449, uv1)
  
let (mk_eq2 :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____477 = FStar_Syntax_Util.type_u ()  in
        match uu____477 with
        | (t_type,u) ->
            let uu____484 =
              let uu____489 = FStar_TypeChecker_Env.all_binders env  in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____489 t_type  in
            (match uu____484 with
             | (tt,uu____491) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
  
type uvi =
  | TERM of
  ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____524 -> false
  
let (__proj__TERM__item___0 :
  uvi ->
    ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
       FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____564 -> false
  
let (__proj__UNIV__item___0 :
  uvi ->
    (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UNIV _0 -> _0 
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list
    ;
  ctr: Prims.int ;
  defer_ok: Prims.bool ;
  smt_ok: Prims.bool ;
  tcenv: FStar_TypeChecker_Env.env }[@@deriving show]
let (__proj__Mkworklist__item__attempting :
  worklist -> FStar_TypeChecker_Common.probs) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__attempting
  
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__wl_deferred
  
let (__proj__Mkworklist__item__ctr : worklist -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} -> __fname__ctr
  
let (__proj__Mkworklist__item__defer_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__defer_ok
  
let (__proj__Mkworklist__item__smt_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__smt_ok
  
let (__proj__Mkworklist__item__tcenv : worklist -> FStar_TypeChecker_Env.env)
  =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} -> __fname__tcenv
  
type solution =
  | Success of FStar_TypeChecker_Common.deferred 
  | Failed of (FStar_TypeChecker_Common.prob,Prims.string)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____750 -> false
  
let (__proj__Success__item___0 :
  solution -> FStar_TypeChecker_Common.deferred) =
  fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____766 -> false
  
let (__proj__Failed__item___0 :
  solution ->
    (FStar_TypeChecker_Common.prob,Prims.string)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT [@@deriving show]
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____789 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____793 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
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
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___84_820  ->
    match uu___84_820 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let compact = FStar_Syntax_Print.term_to_string t  in
    let detail =
      let uu____826 =
        let uu____827 = FStar_Syntax_Subst.compress t  in
        uu____827.FStar_Syntax_Syntax.n  in
      match uu____826 with
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let uu____856 = FStar_Syntax_Print.uvar_to_string u  in
          let uu____857 = FStar_Syntax_Print.term_to_string t1  in
          FStar_Util.format2 "%s : %s" uu____856 uu____857
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
             FStar_Syntax_Syntax.pos = uu____860;
             FStar_Syntax_Syntax.vars = uu____861;_},args)
          ->
          let uu____907 = FStar_Syntax_Print.uvar_to_string u  in
          let uu____908 = FStar_Syntax_Print.term_to_string ty  in
          let uu____909 = FStar_Syntax_Print.args_to_string args  in
          FStar_Util.format3 "(%s : %s) %s" uu____907 uu____908 uu____909
      | uu____910 -> "--"  in
    let uu____911 = FStar_Syntax_Print.tag_of_term t  in
    FStar_Util.format3 "%s (%s)\t%s" compact uu____911 detail
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___85_917  ->
      match uu___85_917 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____923 =
            let uu____926 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____927 =
              let uu____930 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____931 =
                let uu____934 =
                  let uu____937 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____937]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____934
                 in
              uu____930 :: uu____931  in
            uu____926 :: uu____927  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s" uu____923
      | FStar_TypeChecker_Common.CProb p ->
          let uu____943 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____944 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____945 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____943 uu____944
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____945
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___86_951  ->
      match uu___86_951 with
      | UNIV (u,t) ->
          let x =
            let uu____955 = FStar_Options.hide_uvar_nums ()  in
            if uu____955
            then "?"
            else
              (let uu____957 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____957 FStar_Util.string_of_int)
             in
          let uu____958 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____958
      | TERM ((u,uu____960),t) ->
          let x =
            let uu____967 = FStar_Options.hide_uvar_nums ()  in
            if uu____967
            then "?"
            else
              (let uu____969 = FStar_Syntax_Unionfind.uvar_id u  in
               FStar_All.pipe_right uu____969 FStar_Util.string_of_int)
             in
          let uu____970 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____970
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____981 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____981 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____993 =
      let uu____996 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____996
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____993 (FStar_String.concat ", ")
  
let args_to_string :
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
              | (x,uu____1048) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1024 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    let uu____1054 =
      let uu____1055 = FStar_Options.eager_inference ()  in
      Prims.op_Negation uu____1055  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1054;
      smt_ok = true;
      tcenv = env
    }
  
let (singleton' :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.bool -> worklist)
  =
  fun env  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___118_1071 = empty_worklist env  in
        {
          attempting = [prob];
          wl_deferred = (uu___118_1071.wl_deferred);
          ctr = (uu___118_1071.ctr);
          defer_ok = (uu___118_1071.defer_ok);
          smt_ok;
          tcenv = (uu___118_1071.tcenv)
        }
  
let (singleton :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist) =
  fun env  -> fun prob  -> singleton' env prob true 
let wl_of_guard :
  'Auu____1081 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1081,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___119_1102 = empty_worklist env  in
      let uu____1103 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1103;
        wl_deferred = (uu___119_1102.wl_deferred);
        ctr = (uu___119_1102.ctr);
        defer_ok = false;
        smt_ok = (uu___119_1102.smt_ok);
        tcenv = (uu___119_1102.tcenv)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___120_1117 = wl  in
        {
          attempting = (uu___120_1117.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___120_1117.ctr);
          defer_ok = (uu___120_1117.defer_ok);
          smt_ok = (uu___120_1117.smt_ok);
          tcenv = (uu___120_1117.tcenv)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      let uu___121_1134 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___121_1134.wl_deferred);
        ctr = (uu___121_1134.ctr);
        defer_ok = (uu___121_1134.defer_ok);
        smt_ok = (uu___121_1134.smt_ok);
        tcenv = (uu___121_1134.tcenv)
      }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1145 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1145
         then
           let uu____1146 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1146
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___87_1150  ->
    match uu___87_1150 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1154 'Auu____1155 .
    ('Auu____1155,'Auu____1154) FStar_TypeChecker_Common.problem ->
      ('Auu____1155,'Auu____1154) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___122_1172 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___122_1172.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___122_1172.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___122_1172.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___122_1172.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___122_1172.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___122_1172.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___122_1172.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1180 'Auu____1181 .
    ('Auu____1181,'Auu____1180) FStar_TypeChecker_Common.problem ->
      ('Auu____1181,'Auu____1180) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___88_1201  ->
    match uu___88_1201 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.CProb _0_42)
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___89_1225  ->
      match uu___89_1225 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___90_1228  ->
    match uu___90_1228 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___91_1241  ->
    match uu___91_1241 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___92_1256  ->
    match uu___92_1256 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___93_1271  ->
    match uu___93_1271 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_guard :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___94_1288  ->
    match uu___94_1288 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_scope : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders)
  =
  fun uu___95_1305  ->
    match uu___95_1305 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___96_1318  ->
    match uu___96_1318 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1340 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1340 = (Prims.parse_int "1")
  
let (next_pid : Prims.unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1352  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____1567 'Auu____1568 .
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob ->
        'Auu____1568 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1568 ->
              'Auu____1567 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1568,'Auu____1567)
                    FStar_TypeChecker_Common.problem
  =
  fun scope  ->
    fun orig  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun reason  ->
                let uu____1605 = next_pid ()  in
                let uu____1606 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0
                   in
                {
                  FStar_TypeChecker_Common.pid = uu____1605;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1606;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
  
let new_problem :
  'Auu____1620 'Auu____1621 .
    FStar_TypeChecker_Env.env ->
      'Auu____1621 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1621 ->
            'Auu____1620 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1621,'Auu____1620)
                    FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              fun reason  ->
                let scope = FStar_TypeChecker_Env.all_binders env  in
                let uu____1659 = next_pid ()  in
                let uu____1660 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0
                   in
                {
                  FStar_TypeChecker_Common.pid = uu____1659;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1660;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = [reason];
                  FStar_TypeChecker_Common.loc = loc;
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
  
let problem_using_guard :
  'Auu____1673 'Auu____1674 .
    FStar_TypeChecker_Common.prob ->
      'Auu____1674 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1674 ->
            'Auu____1673 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____1674,'Auu____1673) FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____1707 = next_pid ()  in
              {
                FStar_TypeChecker_Common.pid = uu____1707;
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
  'Auu____1713 .
    worklist ->
      ('Auu____1713,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
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
                  x.FStar_Syntax_Syntax.sort
                 in
              FStar_Syntax_Util.mk_forall u x phi
          | FStar_Pervasives_Native.Some e ->
              FStar_Syntax_Subst.subst [FStar_Syntax_Syntax.NT (x, e)] phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____1763 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel")
           in
        if uu____1763
        then
          let uu____1764 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____1765 = prob_to_string env d  in
          let uu____1766 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1764 uu____1765 uu____1766 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1772 -> failwith "impossible"  in
           let uu____1773 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1787 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____1788 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____1787, uu____1788)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1794 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____1795 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____1794, uu____1795)
              in
           match uu____1773 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> Prims.unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___97_1811  ->
            match uu___97_1811 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1823 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1825),t) -> FStar_Syntax_Util.set_uvar u t))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___98_1845  ->
           match uu___98_1845 with
           | UNIV uu____1848 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1854),t) ->
               let uu____1860 = FStar_Syntax_Unionfind.equiv uv u  in
               if uu____1860
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None)
  
let (find_univ_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___99_1880  ->
           match uu___99_1880 with
           | UNIV (u',t) ->
               let uu____1885 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____1885
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1889 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____1896 =
        let uu____1897 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____1897
         in
      FStar_Syntax_Subst.compress uu____1896
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____1904 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____1904
  
let norm_arg :
  'Auu____1908 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____1908) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1908)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____1929 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____1929, (FStar_Pervasives_Native.snd t))
  
let (sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1960  ->
              match uu____1960 with
              | (x,imp) ->
                  let uu____1971 =
                    let uu___123_1972 = x  in
                    let uu____1973 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___123_1972.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___123_1972.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1973
                    }  in
                  (uu____1971, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1988 = aux u3  in FStar_Syntax_Syntax.U_succ uu____1988
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1992 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____1992
        | uu____1995 -> u2  in
      let uu____1996 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1996
  
let (base_and_refinement_maybe_delta :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.bv,
                                                                FStar_Syntax_Syntax.term'
                                                                  FStar_Syntax_Syntax.syntax)
                                                                FStar_Pervasives_Native.tuple2
                                                                FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2)
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
              FStar_TypeChecker_Normalize.HNF]
             in
          FStar_TypeChecker_Normalize.normalize_refinement steps env1 t  in
        let rec aux norm1 t11 =
          let t12 = FStar_Syntax_Util.unmeta t11  in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm1
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____2108 = norm_refinement env t12  in
                 match uu____2108 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2125;
                     FStar_Syntax_Syntax.vars = uu____2126;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2152 =
                       let uu____2153 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____2154 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2153 uu____2154
                        in
                     failwith uu____2152)
          | FStar_Syntax_Syntax.Tm_uinst uu____2169 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2206 =
                   let uu____2207 = FStar_Syntax_Subst.compress t1'  in
                   uu____2207.FStar_Syntax_Syntax.n  in
                 match uu____2206 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2224 -> aux true t1'
                 | uu____2231 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2246 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2277 =
                   let uu____2278 = FStar_Syntax_Subst.compress t1'  in
                   uu____2278.FStar_Syntax_Syntax.n  in
                 match uu____2277 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2295 -> aux true t1'
                 | uu____2302 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2317 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2362 =
                   let uu____2363 = FStar_Syntax_Subst.compress t1'  in
                   uu____2363.FStar_Syntax_Syntax.n  in
                 match uu____2362 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2380 -> aux true t1'
                 | uu____2387 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2402 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2417 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2432 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2447 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2462 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2489 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2520 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2551 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____2578 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____2615 ->
              let uu____2622 =
                let uu____2623 = FStar_Syntax_Print.term_to_string t12  in
                let uu____2624 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2623 uu____2624
                 in
              failwith uu____2622
          | FStar_Syntax_Syntax.Tm_ascribed uu____2639 ->
              let uu____2666 =
                let uu____2667 = FStar_Syntax_Print.term_to_string t12  in
                let uu____2668 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2667 uu____2668
                 in
              failwith uu____2666
          | FStar_Syntax_Syntax.Tm_delayed uu____2683 ->
              let uu____2708 =
                let uu____2709 = FStar_Syntax_Print.term_to_string t12  in
                let uu____2710 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2709 uu____2710
                 in
              failwith uu____2708
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____2725 =
                let uu____2726 = FStar_Syntax_Print.term_to_string t12  in
                let uu____2727 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2726 uu____2727
                 in
              failwith uu____2725
           in
        let uu____2742 = whnf env t1  in aux false uu____2742
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let normalize_refinement :
  'Auu____2764 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____2764 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun steps  ->
    fun env  ->
      fun wl  ->
        fun t0  ->
          FStar_TypeChecker_Normalize.normalize_refinement steps env t0
  
let (unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun t  ->
      let uu____2787 = base_and_refinement env t  in
      FStar_All.pipe_right uu____2787 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____2821 = FStar_Syntax_Syntax.null_bv t  in
    (uu____2821, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____2827 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____2827 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____2848 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____2848 with
          | (t_base,refinement) ->
              (match refinement with
               | FStar_Pervasives_Native.None  -> trivial_refinement t_base
               | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                              FStar_Pervasives_Native.tuple2
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun uu____2927  ->
    match uu____2927 with
    | (t_base,refopt) ->
        let uu____2954 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____2954 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____2986 =
      let uu____2989 =
        let uu____2992 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3015  ->
                  match uu____3015 with | (uu____3022,uu____3023,x) -> x))
           in
        FStar_List.append wl.attempting uu____2992  in
      FStar_List.map (wl_prob_to_string wl) uu____2989  in
    FStar_All.pipe_right uu____2986 (FStar_String.concat "\n\t")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3036 =
          let uu____3049 =
            let uu____3050 = FStar_Syntax_Subst.compress k  in
            uu____3050.FStar_Syntax_Syntax.n  in
          match uu____3049 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3103 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____3103)
              else
                (let uu____3117 = FStar_Syntax_Util.abs_formals t  in
                 match uu____3117 with
                 | (ys',t1,uu____3140) ->
                     let uu____3145 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____3145))
          | uu____3186 ->
              let uu____3187 =
                let uu____3198 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____3198)  in
              ((ys, t), uu____3187)
           in
        match uu____3036 with
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
                 let uu____3247 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____3247 c  in
               FStar_Syntax_Util.abs ys1 t1
                 (FStar_Pervasives_Native.Some
                    (FStar_Syntax_Util.residual_comp_of_comp c1)))
  
let (solve_prob' :
  Prims.bool ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        uvi Prims.list -> worklist -> worklist)
  =
  fun resolve_ok  ->
    fun prob  ->
      fun logical_guard  ->
        fun uvis  ->
          fun wl  ->
            let phi =
              match logical_guard with
              | FStar_Pervasives_Native.None  -> FStar_Syntax_Util.t_true
              | FStar_Pervasives_Native.Some phi -> phi  in
            let uu____3275 = p_guard prob  in
            match uu____3275 with
            | (uu____3280,uv) ->
                ((let uu____3283 =
                    let uu____3284 = FStar_Syntax_Subst.compress uv  in
                    uu____3284.FStar_Syntax_Syntax.n  in
                  match uu____3283 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob  in
                      let phi1 = u_abs k bs phi  in
                      ((let uu____3316 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel")
                           in
                        if uu____3316
                        then
                          let uu____3317 =
                            FStar_Util.string_of_int (p_pid prob)  in
                          let uu____3318 =
                            FStar_Syntax_Print.term_to_string uv  in
                          let uu____3319 =
                            FStar_Syntax_Print.term_to_string phi1  in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3317
                            uu____3318 uu____3319
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____3321 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___124_3324 = wl  in
                  {
                    attempting = (uu___124_3324.attempting);
                    wl_deferred = (uu___124_3324.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___124_3324.defer_ok);
                    smt_ok = (uu___124_3324.smt_ok);
                    tcenv = (uu___124_3324.tcenv)
                  }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3339 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck")
            in
         if uu____3339
         then
           let uu____3340 = FStar_Util.string_of_int pid  in
           let uu____3341 =
             let uu____3342 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____3342 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3340 uu____3341
         else ());
        commit sol;
        (let uu___125_3349 = wl  in
         {
           attempting = (uu___125_3349.attempting);
           wl_deferred = (uu___125_3349.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___125_3349.defer_ok);
           smt_ok = (uu___125_3349.smt_ok);
           tcenv = (uu___125_3349.tcenv)
         })
  
let (solve_prob :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      uvi Prims.list -> worklist -> worklist)
  =
  fun prob  ->
    fun logical_guard  ->
      fun uvis  ->
        fun wl  ->
          let conj_guard1 t g =
            match (t, g) with
            | (uu____3387,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3399 = FStar_Syntax_Util.mk_conj t1 f  in
                FStar_Pervasives_Native.Some uu____3399
             in
          (let uu____3405 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck")
              in
           if uu____3405
           then
             let uu____3406 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____3407 =
               let uu____3408 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____3408 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____3406 uu____3407
           else ());
          solve_prob' false prob logical_guard uvis wl
  
let rec occurs :
  'b .
    worklist ->
      (FStar_Syntax_Syntax.uvar,'b) FStar_Pervasives_Native.tuple2 ->
        FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun wl  ->
    fun uk  ->
      fun t  ->
        let uu____3440 =
          let uu____3447 = FStar_Syntax_Free.uvars t  in
          FStar_All.pipe_right uu____3447 FStar_Util.set_elements  in
        FStar_All.pipe_right uu____3440
          (FStar_Util.for_some
             (fun uu____3483  ->
                match uu____3483 with
                | (uv,uu____3489) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
  
let occurs_check :
  'Auu____3496 'Auu____3497 .
    'Auu____3497 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3496)
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
            let uu____3529 = occurs wl uk t  in Prims.op_Negation uu____3529
             in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3536 =
                 let uu____3537 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk)
                    in
                 let uu____3538 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3537 uu____3538
                  in
               FStar_Pervasives_Native.Some uu____3536)
             in
          (occurs_ok, msg)
  
let occurs_and_freevars_check :
  'Auu____3548 'Auu____3549 .
    'Auu____3549 ->
      worklist ->
        (FStar_Syntax_Syntax.uvar,'Auu____3548)
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
            let fvs_t = FStar_Syntax_Free.names t  in
            let uu____3603 = occurs_check env wl uk t  in
            match uu____3603 with
            | (occurs_ok,msg) ->
                let uu____3634 = FStar_Util.set_is_subset_of fvs_t fvs  in
                (occurs_ok, uu____3634, (msg, fvs, fvs_t))
  
let intersect_vars :
  'Auu____3657 'Auu____3658 .
    (FStar_Syntax_Syntax.bv,'Auu____3658) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3657) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.bv,'Auu____3657) FStar_Pervasives_Native.tuple2
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
             FStar_Syntax_Syntax.no_names)
         in
      let v1_set = as_set1 v1  in
      let uu____3742 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3796  ->
                fun uu____3797  ->
                  match (uu____3796, uu____3797) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____3878 =
                        let uu____3879 = FStar_Util.set_mem x v1_set  in
                        FStar_All.pipe_left Prims.op_Negation uu____3879  in
                      if uu____3878
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort
                            in
                         let uu____3904 =
                           FStar_Util.set_is_subset_of fvs isect_set  in
                         if uu____3904
                         then
                           let uu____3917 = FStar_Util.set_add x isect_set
                              in
                           (((x, imp) :: isect), uu____3917)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names))
         in
      match uu____3742 with | (isect,uu____3958) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____3983 'Auu____3984 .
    (FStar_Syntax_Syntax.bv,'Auu____3984) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3983) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____4039  ->
              fun uu____4040  ->
                match (uu____4039, uu____4040) with
                | ((a,uu____4058),(b,uu____4060)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let pat_var_opt :
  'Auu____4074 'Auu____4075 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____4075) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____4074)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____4074)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun arg  ->
        let hd1 = norm_arg env arg  in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4126 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4140  ->
                      match uu____4140 with
                      | (b,uu____4146) -> FStar_Syntax_Syntax.bv_eq a b))
               in
            if uu____4126
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4162 -> FStar_Pervasives_Native.None
  
let rec (pat_vars :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun seen  ->
      fun args  ->
        match args with
        | [] -> FStar_Pervasives_Native.Some (FStar_List.rev seen)
        | hd1::rest ->
            let uu____4235 = pat_var_opt env seen hd1  in
            (match uu____4235 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4249 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel")
                      in
                   if uu____4249
                   then
                     let uu____4250 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1)
                        in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4250
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4268 =
      let uu____4269 = FStar_Syntax_Subst.compress t  in
      uu____4269.FStar_Syntax_Syntax.n  in
    match uu____4268 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4272 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4289;
           FStar_Syntax_Syntax.pos = uu____4290;
           FStar_Syntax_Syntax.vars = uu____4291;_},uu____4292)
        -> true
    | uu____4329 -> false
  
let (destruct_flex_t :
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
      FStar_Pervasives_Native.tuple4)
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
           FStar_Syntax_Syntax.pos = uu____4453;
           FStar_Syntax_Syntax.vars = uu____4454;_},args)
        -> (t, uv, k, args)
    | uu____4522 -> failwith "Not a flex-uvar"
  
let (destruct_flex_pattern :
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
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun t  ->
      let uu____4599 = destruct_flex_t t  in
      match uu____4599 with
      | (t1,uv,k,args) ->
          let uu____4714 = pat_vars env [] args  in
          (match uu____4714 with
           | FStar_Pervasives_Native.Some vars ->
               ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
           | uu____4812 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
  
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | HeadMatch 
  | FullMatch [@@deriving show]
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____4893 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____4928 -> false
  
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____4932 -> false
  
let (head_match : match_result -> match_result) =
  fun uu___100_4935  ->
    match uu___100_4935 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____4950 -> HeadMatch
  
let (and_match :
  match_result -> (Prims.unit -> match_result) -> match_result) =
  fun m1  ->
    fun m2  ->
      match m1 with
      | MisMatch (i,j) -> MisMatch (i, j)
      | HeadMatch  ->
          let uu____4976 = m2 ()  in
          (match uu____4976 with
           | MisMatch (i,j) -> MisMatch (i, j)
           | uu____4991 -> HeadMatch)
      | FullMatch  -> m2 ()
  
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____5000 ->
          let uu____5001 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____5001 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____5012 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
  
let rec (delta_depth_of_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____5031 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5040 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5067 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5068 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5069 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5086 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5099 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5123) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5129,uu____5130) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5172) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5193;
             FStar_Syntax_Syntax.index = uu____5194;
             FStar_Syntax_Syntax.sort = t2;_},uu____5196)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5203 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5204 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5205 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5218 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5236 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____5236
  
let rec (head_matches :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> match_result)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let t11 = FStar_Syntax_Util.unmeta t1  in
        let t21 = FStar_Syntax_Util.unmeta t2  in
        match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____5263 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____5263
            then FullMatch
            else
              (let uu____5265 =
                 let uu____5274 =
                   let uu____5277 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____5277  in
                 let uu____5278 =
                   let uu____5281 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____5281  in
                 (uu____5274, uu____5278)  in
               MisMatch uu____5265)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5287),FStar_Syntax_Syntax.Tm_uinst (g,uu____5289)) ->
            let uu____5298 = head_matches env f g  in
            FStar_All.pipe_right uu____5298 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5301 = FStar_Const.eq_const c d  in
            if uu____5301
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5308),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5310)) ->
            let uu____5359 = FStar_Syntax_Unionfind.equiv uv uv'  in
            if uu____5359
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5366),FStar_Syntax_Syntax.Tm_refine (y,uu____5368)) ->
            let uu____5377 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5377 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5379),uu____5380) ->
            let uu____5385 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____5385 head_match
        | (uu____5386,FStar_Syntax_Syntax.Tm_refine (x,uu____5388)) ->
            let uu____5393 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5393 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5394,FStar_Syntax_Syntax.Tm_type
           uu____5395) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5396,FStar_Syntax_Syntax.Tm_arrow uu____5397) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            if (FStar_List.length bs1) = (FStar_List.length bs2)
            then
              let uu____5526 =
                let uu____5527 = FStar_List.zip bs1 bs2  in
                let uu____5562 = head_matches env t12 t22  in
                FStar_List.fold_right
                  (fun uu____5571  ->
                     fun a  ->
                       match uu____5571 with
                       | (b1,b2) ->
                           and_match a
                             (fun uu____5580  -> branch_matches env b1 b2))
                  uu____5527 uu____5562
                 in
              FStar_All.pipe_right uu____5526 head_match
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5587),FStar_Syntax_Syntax.Tm_app (head',uu____5589))
            ->
            let uu____5630 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____5630 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5632),uu____5633) ->
            let uu____5654 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____5654 head_match
        | (uu____5655,FStar_Syntax_Syntax.Tm_app (head1,uu____5657)) ->
            let uu____5678 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____5678 head_match
        | uu____5679 ->
            let uu____5684 =
              let uu____5693 = delta_depth_of_term env t11  in
              let uu____5696 = delta_depth_of_term env t21  in
              (uu____5693, uu____5696)  in
            MisMatch uu____5684

and (branch_matches :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch -> match_result)
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
          | (uu____5748,uu____5749) -> false  in
        let uu____5758 = b1  in
        match uu____5758 with
        | (p1,w1,t1) ->
            let uu____5778 = b2  in
            (match uu____5778 with
             | (p2,w2,t2) ->
                 let uu____5798 = FStar_Syntax_Syntax.eq_pat p1 p2  in
                 if uu____5798
                 then
                   let uu____5799 =
                     (let uu____5802 = FStar_Syntax_Util.eq_tm t1 t2  in
                      uu____5802 = FStar_Syntax_Util.Equal) &&
                       (related_by
                          (fun t11  ->
                             fun t21  ->
                               let uu____5811 =
                                 FStar_Syntax_Util.eq_tm t11 t21  in
                               uu____5811 = FStar_Syntax_Util.Equal) w1 w2)
                      in
                   (if uu____5799
                    then FullMatch
                    else
                      MisMatch
                        (FStar_Pervasives_Native.None,
                          FStar_Pervasives_Native.None))
                 else
                   MisMatch
                     (FStar_Pervasives_Native.None,
                       FStar_Pervasives_Native.None))

let head_matches_delta :
  'Auu____5827 .
    FStar_TypeChecker_Env.env ->
      'Auu____5827 ->
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
            let uu____5860 = FStar_Syntax_Util.head_and_args t  in
            match uu____5860 with
            | (head1,uu____5878) ->
                let uu____5899 =
                  let uu____5900 = FStar_Syntax_Util.un_uinst head1  in
                  uu____5900.FStar_Syntax_Syntax.n  in
                (match uu____5899 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5906 =
                       let uu____5907 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       FStar_All.pipe_right uu____5907 FStar_Option.isSome
                        in
                     if uu____5906
                     then
                       let uu____5926 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t
                          in
                       FStar_All.pipe_right uu____5926
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                     else FStar_Pervasives_Native.None
                 | uu____5930 -> FStar_Pervasives_Native.None)
             in
          let success d r t11 t21 =
            (r,
              (if d > (Prims.parse_int "0")
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let fail r = (r, FStar_Pervasives_Native.None)  in
          let rec aux retry n_delta t11 t21 =
            let r = head_matches env t11 t21  in
            match r with
            | MisMatch
                (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ),uu____6033)
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____6051 =
                     let uu____6060 = maybe_inline t11  in
                     let uu____6063 = maybe_inline t21  in
                     (uu____6060, uu____6063)  in
                   match uu____6051 with
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
                (uu____6100,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____6118 =
                     let uu____6127 = maybe_inline t11  in
                     let uu____6130 = maybe_inline t21  in
                     (uu____6127, uu____6130)  in
                   match uu____6118 with
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
                let uu____6173 = FStar_TypeChecker_Common.decr_delta_depth d1
                   in
                (match uu____6173 with
                 | FStar_Pervasives_Native.None  -> fail r
                 | FStar_Pervasives_Native.Some d ->
                     let t12 =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d;
                         FStar_TypeChecker_Normalize.Weak;
                         FStar_TypeChecker_Normalize.HNF] env wl t11
                        in
                     let t22 =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d;
                         FStar_TypeChecker_Normalize.Weak;
                         FStar_TypeChecker_Normalize.HNF] env wl t21
                        in
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch
                (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some
                 d2)
                ->
                let d1_greater_than_d2 =
                  FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
                let uu____6196 =
                  if d1_greater_than_d2
                  then
                    let t1' =
                      normalize_refinement
                        [FStar_TypeChecker_Normalize.UnfoldUntil d2;
                        FStar_TypeChecker_Normalize.Weak;
                        FStar_TypeChecker_Normalize.HNF] env wl t11
                       in
                    (t1', t21)
                  else
                    (let t2' =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                         FStar_TypeChecker_Normalize.Weak;
                         FStar_TypeChecker_Normalize.HNF] env wl t21
                        in
                     (t11, t2'))
                   in
                (match uu____6196 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6220 -> fail r
            | uu____6229 -> success n_delta r t11 t21  in
          aux true (Prims.parse_int "0") t1 t2
  
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | C of FStar_Syntax_Syntax.comp [@@deriving show]
let (uu___is_T : tc -> Prims.bool) =
  fun projectee  -> match projectee with | T _0 -> true | uu____6262 -> false 
let (__proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | T _0 -> _0 
let (uu___is_C : tc -> Prims.bool) =
  fun projectee  -> match projectee with | C _0 -> true | uu____6298 -> false 
let (__proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp) =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list[@@deriving show]
let (tc_to_string : tc -> Prims.string) =
  fun uu___101_6310  ->
    match uu___101_6310 with
    | T (t,uu____6312) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
  
let (generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6328 = FStar_Syntax_Util.type_u ()  in
      match uu____6328 with
      | (t,uu____6334) ->
          let uu____6335 = new_uvar r binders t  in
          FStar_Pervasives_Native.fst uu____6335
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6346 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____6346 FStar_Pervasives_Native.fst
  
let rec (decompose :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (tc Prims.list -> FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term ->
                                                   Prims.bool,(FStar_Syntax_Syntax.binder
                                                                 FStar_Pervasives_Native.option,
                                                                variance,
                                                                tc)
                                                                FStar_Pervasives_Native.tuple3
                                                                Prims.list)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let matches t' =
        let uu____6410 = head_matches env t1 t'  in
        match uu____6410 with
        | MisMatch uu____6411 -> false
        | uu____6420 -> true  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6516,imp),T (t2,uu____6519)) -> (t2, imp)
                     | uu____6538 -> failwith "Bad reconstruction") args
                args'
               in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6605  ->
                    match uu____6605 with
                    | (t2,uu____6619) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6662 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6662 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6737))::tcs2) ->
                       aux
                         (((let uu___126_6772 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___126_6772.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___126_6772.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6790 -> failwith "Bad reconstruction"  in
                 aux [] bs1 tcs  in
               let rec decompose1 out uu___102_6843 =
                 match uu___102_6843 with
                 | [] ->
                     FStar_List.rev
                       ((FStar_Pervasives_Native.None, COVARIANT, (C c1)) ::
                       out)
                 | hd1::rest ->
                     decompose1
                       (((FStar_Pervasives_Native.Some hd1), CONTRAVARIANT,
                          (T
                             (((FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest
                  in
               let uu____6960 = decompose1 [] bs1  in
               (rebuild, matches, uu____6960))
      | uu____7009 ->
          let rebuild uu___103_7015 =
            match uu___103_7015 with
            | [] -> t1
            | uu____7018 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
  
let (un_T : tc -> FStar_Syntax_Syntax.term) =
  fun uu___104_7049  ->
    match uu___104_7049 with
    | T (t,uu____7051) -> t
    | uu____7060 -> failwith "Impossible"
  
let (arg_of_tc : tc -> FStar_Syntax_Syntax.arg) =
  fun uu___105_7063  ->
    match uu___105_7063 with
    | T (t,uu____7065) -> FStar_Syntax_Syntax.as_arg t
    | uu____7074 -> failwith "Impossible"
  
let (imitation_sub_probs :
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.args ->
          (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,
            variance,tc) FStar_Pervasives_Native.tuple3 Prims.list ->
            (FStar_TypeChecker_Common.prob Prims.list,tc Prims.list,FStar_Syntax_Syntax.formula)
              FStar_Pervasives_Native.tuple3)
  =
  fun orig  ->
    fun env  ->
      fun scope  ->
        fun ps  ->
          fun qs  ->
            let r = p_loc orig  in
            let rel = p_rel orig  in
            let sub_prob scope1 args q =
              match q with
              | (uu____7180,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r  in
                  let uu____7205 = new_uvar r scope1 k  in
                  (match uu____7205 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7223 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r
                          in
                       let uu____7240 =
                         let uu____7241 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm"
                            in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____7241
                          in
                       ((T (gi_xs, mk_kind)), uu____7240))
              | (uu____7254,uu____7255,C uu____7256) -> failwith "impos"  in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7403 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7420;
                         FStar_Syntax_Syntax.vars = uu____7421;_})
                        ->
                        let uu____7444 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____7444 with
                         | (T (gi_xs,uu____7468),prob) ->
                             let uu____7478 =
                               let uu____7479 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____7479
                                in
                             (uu____7478, [prob])
                         | uu____7482 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7497;
                         FStar_Syntax_Syntax.vars = uu____7498;_})
                        ->
                        let uu____7521 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____7521 with
                         | (T (gi_xs,uu____7545),prob) ->
                             let uu____7555 =
                               let uu____7556 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                                  in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____7556
                                in
                             (uu____7555, [prob])
                         | uu____7559 -> failwith "impossible")
                    | (uu____7570,uu____7571,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7573;
                         FStar_Syntax_Syntax.vars = uu____7574;_})
                        ->
                        let components =
                          FStar_All.pipe_right
                            c.FStar_Syntax_Syntax.effect_args
                            (FStar_List.map
                               (fun t  ->
                                  (FStar_Pervasives_Native.None, INVARIANT,
                                    (T
                                       ((FStar_Pervasives_Native.fst t),
                                         generic_kind)))))
                           in
                        let components1 =
                          (FStar_Pervasives_Native.None, COVARIANT,
                            (T
                               ((c.FStar_Syntax_Syntax.result_typ),
                                 kind_type)))
                          :: components  in
                        let uu____7705 =
                          let uu____7714 =
                            FStar_List.map (sub_prob scope1 args) components1
                             in
                          FStar_All.pipe_right uu____7714 FStar_List.unzip
                           in
                        (match uu____7705 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7768 =
                                 let uu____7769 =
                                   let uu____7772 = FStar_List.hd tcs  in
                                   FStar_All.pipe_right uu____7772 un_T  in
                                 let uu____7773 =
                                   let uu____7782 = FStar_List.tl tcs  in
                                   FStar_All.pipe_right uu____7782
                                     (FStar_List.map arg_of_tc)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7769;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7773;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 }  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7768
                                in
                             ((C gi_xs), sub_probs))
                    | uu____7791 ->
                        let uu____7804 = sub_prob scope1 args q  in
                        (match uu____7804 with
                         | (ktec,prob) -> (ktec, [prob]))
                     in
                  (match uu____7403 with
                   | (tc,probs) ->
                       let uu____7835 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7898,uu____7899),T
                            (t,uu____7901)) ->
                             let b1 =
                               ((let uu___127_7938 = b  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___127_7938.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___127_7938.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp)
                                in
                             let uu____7939 =
                               let uu____7946 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1
                                  in
                               uu____7946 :: args  in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7939)
                         | uu____7981 ->
                             (FStar_Pervasives_Native.None, scope1, args)
                          in
                       (match uu____7835 with
                        | (bopt,scope2,args1) ->
                            let uu____8065 = aux scope2 args1 qs2  in
                            (match uu____8065 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____8102 =
                                         let uu____8105 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst))
                                            in
                                         f :: uu____8105  in
                                       FStar_Syntax_Util.mk_conj_l uu____8102
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____8128 =
                                         let uu____8131 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f
                                            in
                                         let uu____8132 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst))
                                            in
                                         uu____8131 :: uu____8132  in
                                       FStar_Syntax_Util.mk_conj_l uu____8128
                                    in
                                 ((FStar_List.append probs sub_probs), (tc ::
                                   tcs), f1))))
               in
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
let (rigid_rigid : Prims.int) = (Prims.parse_int "0") 
let (flex_rigid_eq : Prims.int) = (Prims.parse_int "1") 
let (flex_refine_inner : Prims.int) = (Prims.parse_int "2") 
let (flex_refine : Prims.int) = (Prims.parse_int "3") 
let (flex_rigid : Prims.int) = (Prims.parse_int "4") 
let (rigid_flex : Prims.int) = (Prims.parse_int "5") 
let (refine_flex : Prims.int) = (Prims.parse_int "6") 
let (flex_flex : Prims.int) = (Prims.parse_int "7") 
let compress_tprob :
  'Auu____8200 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8200)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8200)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___128_8221 = p  in
      let uu____8226 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8227 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___128_8221.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8226;
        FStar_TypeChecker_Common.relation =
          (uu___128_8221.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8227;
        FStar_TypeChecker_Common.element =
          (uu___128_8221.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___128_8221.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___128_8221.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___128_8221.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___128_8221.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___128_8221.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8239 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____8239
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____8248 -> p
  
let (rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8268 = compress_prob wl pr  in
        FStar_All.pipe_right uu____8268 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8278 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8278 with
           | (lh,uu____8298) ->
               let uu____8319 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8319 with
                | (rh,uu____8339) ->
                    let uu____8360 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8377,FStar_Syntax_Syntax.Tm_uvar uu____8378)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8415,uu____8416)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8437,FStar_Syntax_Syntax.Tm_uvar uu____8438)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8459,uu____8460)
                          ->
                          let uu____8477 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____8477 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8526 ->
                                    let rank =
                                      let uu____8534 = is_top_level_prob prob
                                         in
                                      if uu____8534
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____8536 =
                                      let uu___129_8541 = tp  in
                                      let uu____8546 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___129_8541.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___129_8541.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___129_8541.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8546;
                                        FStar_TypeChecker_Common.element =
                                          (uu___129_8541.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___129_8541.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___129_8541.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___129_8541.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___129_8541.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___129_8541.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____8536)))
                      | (uu____8557,FStar_Syntax_Syntax.Tm_uvar uu____8558)
                          ->
                          let uu____8575 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____8575 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8624 ->
                                    let uu____8631 =
                                      let uu___130_8638 = tp  in
                                      let uu____8643 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___130_8638.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8643;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___130_8638.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___130_8638.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___130_8638.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___130_8638.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___130_8638.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___130_8638.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___130_8638.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___130_8638.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____8631)))
                      | (uu____8660,uu____8661) -> (rigid_rigid, tp)  in
                    (match uu____8360 with
                     | (rank,tp1) ->
                         let uu____8680 =
                           FStar_All.pipe_right
                             (let uu___131_8686 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___131_8686.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___131_8686.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___131_8686.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___131_8686.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___131_8686.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___131_8686.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___131_8686.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___131_8686.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___131_8686.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50)
                            in
                         (rank, uu____8680))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8696 =
            FStar_All.pipe_right
              (let uu___132_8702 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___132_8702.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___132_8702.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___132_8702.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___132_8702.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___132_8702.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___132_8702.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___132_8702.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___132_8702.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___132_8702.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51)
             in
          (rigid_rigid, uu____8696)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun wl  ->
    let rec aux uu____8757 probs =
      match uu____8757 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8810 = rank wl hd1  in
               (match uu____8810 with
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
                      else aux (min_rank, min1, (hd2 :: out)) tl1))
       in
    aux
      ((flex_flex + (Prims.parse_int "1")), FStar_Pervasives_Native.None, [])
      wl.attempting
  
let (is_flex_rigid : Prims.int -> Prims.bool) =
  fun rank1  -> (flex_refine_inner <= rank1) && (rank1 <= flex_rigid) 
let (is_rigid_flex : Prims.int -> Prims.bool) =
  fun rank1  -> (rigid_flex <= rank1) && (rank1 <= refine_flex) 
type univ_eq_sol =
  | UDeferred of worklist 
  | USolved of worklist 
  | UFailed of Prims.string [@@deriving show]
let (uu___is_UDeferred : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____8917 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8929 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8941 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> Prims.string) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let rec (really_solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun pid_orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          let u11 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1  in
          let u21 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2  in
          let rec occurs_univ v1 u =
            match u with
            | FStar_Syntax_Syntax.U_max us ->
                FStar_All.pipe_right us
                  (FStar_Util.for_some
                     (fun u3  ->
                        let uu____8981 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8981 with
                        | (k,uu____8987) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8997 -> false)))
            | uu____8998 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____9049 =
                          really_solve_universe_eq pid_orig wl1 u13 u23  in
                        (match uu____9049 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____9052 -> USolved wl1  in
                  aux wl us1 us2
                else
                  (let uu____9062 =
                     let uu____9063 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____9064 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____9063
                       uu____9064
                      in
                   UFailed uu____9062)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9084 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9084 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9106 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9106 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____9109 ->
                let uu____9114 =
                  let uu____9115 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____9116 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____9115
                    uu____9116 msg
                   in
                UFailed uu____9114
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9117,uu____9118) ->
              let uu____9119 =
                let uu____9120 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9121 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9120 uu____9121
                 in
              failwith uu____9119
          | (FStar_Syntax_Syntax.U_unknown ,uu____9122) ->
              let uu____9123 =
                let uu____9124 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9125 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9124 uu____9125
                 in
              failwith uu____9123
          | (uu____9126,FStar_Syntax_Syntax.U_bvar uu____9127) ->
              let uu____9128 =
                let uu____9129 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9130 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9129 uu____9130
                 in
              failwith uu____9128
          | (uu____9131,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9132 =
                let uu____9133 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9134 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9133 uu____9134
                 in
              failwith uu____9132
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9158 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____9158
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____9180 = occurs_univ v1 u3  in
              if uu____9180
              then
                let uu____9181 =
                  let uu____9182 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9183 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9182 uu____9183
                   in
                try_umax_components u11 u21 uu____9181
              else
                (let uu____9185 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9185)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____9205 = occurs_univ v1 u3  in
              if uu____9205
              then
                let uu____9206 =
                  let uu____9207 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9208 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9207 uu____9208
                   in
                try_umax_components u11 u21 uu____9206
              else
                (let uu____9210 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9210)
          | (FStar_Syntax_Syntax.U_max uu____9219,uu____9220) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9226 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9226
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9228,FStar_Syntax_Syntax.U_max uu____9229) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9235 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9235
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9237,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9238,FStar_Syntax_Syntax.U_name
             uu____9239) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9240) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9241) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9242,FStar_Syntax_Syntax.U_succ
             uu____9243) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9244,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
  
let (solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
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
          FStar_Pervasives_Native.tuple2
  =
  fun bc1  ->
    fun bc2  ->
      let uu____9330 = bc1  in
      match uu____9330 with
      | (bs1,mk_cod1) ->
          let uu____9371 = bc2  in
          (match uu____9371 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____9441 = FStar_Util.first_N n1 bs  in
                 match uu____9441 with
                 | (bs3,rest) ->
                     let uu____9466 = mk_cod rest  in (bs3, uu____9466)
                  in
               let l1 = FStar_List.length bs1  in
               let l2 = FStar_List.length bs2  in
               if l1 = l2
               then
                 let uu____9495 =
                   let uu____9502 = mk_cod1 []  in (bs1, uu____9502)  in
                 let uu____9505 =
                   let uu____9512 = mk_cod2 []  in (bs2, uu____9512)  in
                 (uu____9495, uu____9505)
               else
                 if l1 > l2
                 then
                   (let uu____9554 = curry l2 bs1 mk_cod1  in
                    let uu____9567 =
                      let uu____9574 = mk_cod2 []  in (bs2, uu____9574)  in
                    (uu____9554, uu____9567))
                 else
                   (let uu____9590 =
                      let uu____9597 = mk_cod1 []  in (bs1, uu____9597)  in
                    let uu____9600 = curry l1 bs2 mk_cod2  in
                    (uu____9590, uu____9600)))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____9721 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____9721
       then
         let uu____9722 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9722
       else ());
      (let uu____9724 = next_prob probs  in
       match uu____9724 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___133_9745 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___133_9745.wl_deferred);
               ctr = (uu___133_9745.ctr);
               defer_ok = (uu___133_9745.defer_ok);
               smt_ok = (uu___133_9745.smt_ok);
               tcenv = (uu___133_9745.tcenv)
             }  in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                if
                  ((Prims.op_Negation probs1.defer_ok) &&
                     (flex_refine_inner <= rank1))
                    && (rank1 <= flex_rigid)
                then
                  let uu____9756 = solve_flex_rigid_join env tp probs1  in
                  (match uu____9756 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9761 = solve_rigid_flex_meet env tp probs1  in
                     match uu____9761 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9766,uu____9767) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9784 ->
                let uu____9793 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9852  ->
                          match uu____9852 with
                          | (c,uu____9860,uu____9861) -> c < probs.ctr))
                   in
                (match uu____9793 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9902 =
                            FStar_List.map
                              (fun uu____9917  ->
                                 match uu____9917 with
                                 | (uu____9928,x,y) -> (x, y))
                              probs.wl_deferred
                             in
                          Success uu____9902
                      | uu____9931 ->
                          let uu____9940 =
                            let uu___134_9941 = probs  in
                            let uu____9942 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9963  ->
                                      match uu____9963 with
                                      | (uu____9970,uu____9971,y) -> y))
                               in
                            {
                              attempting = uu____9942;
                              wl_deferred = rest;
                              ctr = (uu___134_9941.ctr);
                              defer_ok = (uu___134_9941.defer_ok);
                              smt_ok = (uu___134_9941.smt_ok);
                              tcenv = (uu___134_9941.tcenv)
                            }  in
                          solve env uu____9940))))

and (solve_one_universe_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> worklist -> solution)
  =
  fun env  ->
    fun orig  ->
      fun u1  ->
        fun u2  ->
          fun wl  ->
            let uu____9978 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____9978 with
            | USolved wl1 ->
                let uu____9980 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____9980
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 -> solve env (defer "" orig wl1)

and (solve_maybe_uinsts :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> worklist -> univ_eq_sol)
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
                  let uu____10026 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10026 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10029 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10041;
                  FStar_Syntax_Syntax.vars = uu____10042;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10045;
                  FStar_Syntax_Syntax.vars = uu____10046;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10060,uu____10061) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10068,FStar_Syntax_Syntax.Tm_uinst uu____10069) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10076 -> USolved wl

and (giveup_or_defer :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> Prims.string -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun msg  ->
          if wl.defer_ok
          then
            ((let uu____10086 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10086
              then
                let uu____10087 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10087 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

and (solve_rigid_flex_meet :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10096 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____10096
         then
           let uu____10097 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____10097
         else ());
        (let uu____10099 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____10099 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____10161 = head_matches_delta env () t1 t2  in
               match uu____10161 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____10202 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____10251 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10266 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____10267 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____10266, uu____10267)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10272 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____10273 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____10272, uu____10273)
                           in
                        (match uu____10251 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____10299 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____10299
                                in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____10330 =
                                    let uu____10339 =
                                      let uu____10342 =
                                        let uu____10345 =
                                          let uu____10346 =
                                            let uu____10353 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2
                                               in
                                            (x, uu____10353)  in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____10346
                                           in
                                        FStar_Syntax_Syntax.mk uu____10345
                                         in
                                      uu____10342
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____10361 =
                                      let uu____10364 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort
                                         in
                                      [uu____10364]  in
                                    (uu____10339, uu____10361)  in
                                  FStar_Pervasives_Native.Some uu____10330
                              | (uu____10377,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10379)) ->
                                  let uu____10384 =
                                    let uu____10391 =
                                      let uu____10394 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11
                                         in
                                      [uu____10394]  in
                                    (t11, uu____10391)  in
                                  FStar_Pervasives_Native.Some uu____10384
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10404),uu____10405) ->
                                  let uu____10410 =
                                    let uu____10417 =
                                      let uu____10420 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21
                                         in
                                      [uu____10420]  in
                                    (t21, uu____10417)  in
                                  FStar_Pervasives_Native.Some uu____10410
                              | uu____10429 ->
                                  let uu____10434 =
                                    FStar_Syntax_Util.head_and_args t11  in
                                  (match uu____10434 with
                                   | (head1,uu____10458) ->
                                       let uu____10479 =
                                         let uu____10480 =
                                           FStar_Syntax_Util.un_uinst head1
                                            in
                                         uu____10480.FStar_Syntax_Syntax.n
                                          in
                                       (match uu____10479 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10491;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10493;_}
                                            ->
                                            let prev =
                                              if i > (Prims.parse_int "1")
                                              then
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                  (i - (Prims.parse_int "1"))
                                              else
                                                FStar_Syntax_Syntax.Delta_constant
                                               in
                                            let t12 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Normalize.Weak;
                                                FStar_TypeChecker_Normalize.HNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t11
                                               in
                                            let t22 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Normalize.Weak;
                                                FStar_TypeChecker_Normalize.HNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t21
                                               in
                                            disjoin t12 t22
                                        | uu____10500 ->
                                            FStar_Pervasives_Native.None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10513) ->
                  let uu____10538 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___106_10564  ->
                            match uu___106_10564 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10571 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____10571 with
                                      | (u',uu____10587) ->
                                          let uu____10608 =
                                            let uu____10609 = whnf env u'  in
                                            uu____10609.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____10608 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10613) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10638 -> false))
                                 | uu____10639 -> false)
                            | uu____10642 -> false))
                     in
                  (match uu____10538 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10676 tps =
                         match uu____10676 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10724 =
                                    let uu____10733 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound uu____10733  in
                                  (match uu____10724 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10768 -> FStar_Pervasives_Native.None)
                          in
                       let uu____10777 =
                         let uu____10786 =
                           let uu____10793 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (uu____10793, [])  in
                         make_lower_bound uu____10786 lower_bounds  in
                       (match uu____10777 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10805 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____10805
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
                                "meeting refinements"
                               in
                            ((let uu____10825 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____10825
                              then
                                let wl' =
                                  let uu___135_10827 = wl  in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___135_10827.wl_deferred);
                                    ctr = (uu___135_10827.ctr);
                                    defer_ok = (uu___135_10827.defer_ok);
                                    smt_ok = (uu___135_10827.smt_ok);
                                    tcenv = (uu___135_10827.tcenv)
                                  }  in
                                let uu____10828 = wl_to_string wl'  in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10828
                              else ());
                             (let uu____10830 =
                                solve_t env eq_prob
                                  (let uu___136_10832 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___136_10832.wl_deferred);
                                     ctr = (uu___136_10832.ctr);
                                     defer_ok = (uu___136_10832.defer_ok);
                                     smt_ok = (uu___136_10832.smt_ok);
                                     tcenv = (uu___136_10832.tcenv)
                                   })
                                 in
                              match uu____10830 with
                              | Success uu____10835 ->
                                  let wl1 =
                                    let uu___137_10837 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___137_10837.wl_deferred);
                                      ctr = (uu___137_10837.ctr);
                                      defer_ok = (uu___137_10837.defer_ok);
                                      smt_ok = (uu___137_10837.smt_ok);
                                      tcenv = (uu___137_10837.tcenv)
                                    }  in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1
                                     in
                                  let uu____10839 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds
                                     in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10844 -> FStar_Pervasives_Native.None))))
              | uu____10845 -> failwith "Impossible: Not a rigid-flex"))

and (solve_flex_rigid_join :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10854 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____10854
         then
           let uu____10855 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10855
         else ());
        (let uu____10857 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____10857 with
         | (u,args) ->
             let uu____10896 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____10896 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i  in
                  let base_types_match t1 t2 =
                    let uu____10937 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____10937 with
                    | (h1,args1) ->
                        let uu____10978 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____10978 with
                         | (h2,uu____10998) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____11025 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  if uu____11025
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____11043 =
                                          let uu____11046 =
                                            let uu____11047 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____11047
                                             in
                                          [uu____11046]  in
                                        FStar_Pervasives_Native.Some
                                          uu____11043))
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
                                       (let uu____11080 =
                                          let uu____11083 =
                                            let uu____11084 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____11084
                                             in
                                          [uu____11083]  in
                                        FStar_Pervasives_Native.Some
                                          uu____11080))
                                  else FStar_Pervasives_Native.None
                              | uu____11098 -> FStar_Pervasives_Native.None))
                     in
                  let conjoin t1 t2 =
                    match ((t1.FStar_Syntax_Syntax.n),
                            (t2.FStar_Syntax_Syntax.n))
                    with
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,phi1),FStar_Syntax_Syntax.Tm_refine (y,phi2)) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort
                            y.FStar_Syntax_Syntax.sort
                           in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             let x1 = FStar_Syntax_Syntax.freshen_bv x  in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x1)]
                                in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1
                                in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2
                                in
                             let uu____11188 =
                               let uu____11197 =
                                 let uu____11200 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21  in
                                 FStar_Syntax_Util.refine x1 uu____11200  in
                               (uu____11197, m1)  in
                             FStar_Pervasives_Native.Some uu____11188)
                    | (uu____11213,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____11215)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____11263),uu____11264) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____11311 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11364) ->
                       let uu____11389 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___107_11415  ->
                                 match uu___107_11415 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____11422 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____11422 with
                                           | (u',uu____11438) ->
                                               let uu____11459 =
                                                 let uu____11460 =
                                                   whnf env u'  in
                                                 uu____11460.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____11459 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11464) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11489 -> false))
                                      | uu____11490 -> false)
                                 | uu____11493 -> false))
                          in
                       (match uu____11389 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11531 tps =
                              match uu____11531 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11593 =
                                         let uu____11604 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound uu____11604  in
                                       (match uu____11593 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11655 ->
                                       FStar_Pervasives_Native.None)
                               in
                            let uu____11666 =
                              let uu____11677 =
                                let uu____11686 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (uu____11686, [])  in
                              make_upper_bound uu____11677 upper_bounds  in
                            (match uu____11666 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11700 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____11700
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
                                     "joining refinements"
                                    in
                                 ((let uu____11726 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____11726
                                   then
                                     let wl' =
                                       let uu___138_11728 = wl  in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___138_11728.wl_deferred);
                                         ctr = (uu___138_11728.ctr);
                                         defer_ok = (uu___138_11728.defer_ok);
                                         smt_ok = (uu___138_11728.smt_ok);
                                         tcenv = (uu___138_11728.tcenv)
                                       }  in
                                     let uu____11729 = wl_to_string wl'  in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11729
                                   else ());
                                  (let uu____11731 =
                                     solve_t env eq_prob
                                       (let uu___139_11733 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___139_11733.wl_deferred);
                                          ctr = (uu___139_11733.ctr);
                                          defer_ok =
                                            (uu___139_11733.defer_ok);
                                          smt_ok = (uu___139_11733.smt_ok);
                                          tcenv = (uu___139_11733.tcenv)
                                        })
                                      in
                                   match uu____11731 with
                                   | Success uu____11736 ->
                                       let wl1 =
                                         let uu___140_11738 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___140_11738.wl_deferred);
                                           ctr = (uu___140_11738.ctr);
                                           defer_ok =
                                             (uu___140_11738.defer_ok);
                                           smt_ok = (uu___140_11738.smt_ok);
                                           tcenv = (uu___140_11738.tcenv)
                                         }  in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1
                                          in
                                       let uu____11740 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds
                                          in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11745 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11746 -> failwith "Impossible: Not a flex-rigid")))

and (solve_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders ->
        FStar_TypeChecker_Common.prob ->
          worklist ->
            (FStar_Syntax_Syntax.binders ->
               FStar_TypeChecker_Env.env ->
                 FStar_Syntax_Syntax.subst_elt Prims.list ->
                   FStar_TypeChecker_Common.prob)
              -> solution)
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
                    let rhs_prob = rhs scope env1 subst1  in
                    ((let uu____11821 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____11821
                      then
                        let uu____11822 = prob_to_string env1 rhs_prob  in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11822
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst
                         in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___141_11876 = hd1  in
                      let uu____11877 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___141_11876.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___141_11876.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11877
                      }  in
                    let hd21 =
                      let uu___142_11881 = hd2  in
                      let uu____11882 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___142_11881.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___142_11881.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11882
                      }  in
                    let prob =
                      let uu____11886 =
                        let uu____11891 =
                          FStar_All.pipe_left invert_rel (p_rel orig)  in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11891 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter"
                         in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____11886
                       in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                    let subst2 =
                      let uu____11902 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1
                         in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11902
                       in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                    let uu____11906 =
                      aux (FStar_List.append scope [(hd12, imp)]) env2 subst2
                        xs1 ys1
                       in
                    (match uu____11906 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11944 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst
                              in
                           let uu____11949 =
                             close_forall env2 [(hd12, imp)] phi  in
                           FStar_Syntax_Util.mk_conj uu____11944 uu____11949
                            in
                         ((let uu____11959 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____11959
                           then
                             let uu____11960 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____11961 =
                               FStar_Syntax_Print.bv_to_string hd12  in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11960 uu____11961
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11984 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch"
                 in
              let scope = p_scope orig  in
              let uu____11994 = aux scope env [] bs1 bs2  in
              match uu____11994 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl
                     in
                  solve env (attempt sub_probs wl1)

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____12018 = compress_tprob wl problem  in
        solve_t' env uu____12018 wl

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____12051 = head_matches_delta env1 wl1 t1 t2  in
          match uu____12051 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____12082,uu____12083) ->
                   let rec may_relate head3 =
                     let uu____12108 =
                       let uu____12109 = FStar_Syntax_Subst.compress head3
                          in
                       uu____12109.FStar_Syntax_Syntax.n  in
                     match uu____12108 with
                     | FStar_Syntax_Syntax.Tm_name uu____12112 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____12113 -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____12136;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_equational ;
                           FStar_Syntax_Syntax.fv_qual = uu____12137;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____12140;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_abstract uu____12141;
                           FStar_Syntax_Syntax.fv_qual = uu____12142;_}
                         ->
                         problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____12146,uu____12147) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____12189) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____12195) ->
                         may_relate t
                     | uu____12200 -> false  in
                   let uu____12201 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok
                      in
                   if uu____12201
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
                                    FStar_Pervasives_Native.None t11
                                   in
                                let u_x =
                                  env1.FStar_TypeChecker_Env.universe_of env1
                                    t11
                                   in
                                let uu____12218 =
                                  let uu____12219 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____12219 t21
                                   in
                                FStar_Syntax_Util.mk_forall u_x x uu____12218
                             in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1)
                        in
                     let uu____12221 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1
                        in
                     solve env1 uu____12221
                   else
                     (let uu____12223 =
                        let uu____12224 =
                          FStar_Syntax_Print.term_to_string head1  in
                        let uu____12225 =
                          FStar_Syntax_Print.term_to_string head2  in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____12224 uu____12225
                         in
                      giveup env1 uu____12223 orig)
               | (uu____12226,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___143_12240 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___143_12240.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___143_12240.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___143_12240.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___143_12240.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___143_12240.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___143_12240.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___143_12240.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___143_12240.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____12241,FStar_Pervasives_Native.None ) ->
                   ((let uu____12253 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____12253
                     then
                       let uu____12254 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12255 = FStar_Syntax_Print.tag_of_term t1
                          in
                       let uu____12256 = FStar_Syntax_Print.term_to_string t2
                          in
                       let uu____12257 = FStar_Syntax_Print.tag_of_term t2
                          in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____12254
                         uu____12255 uu____12256 uu____12257
                     else ());
                    (let uu____12259 = FStar_Syntax_Util.head_and_args t1  in
                     match uu____12259 with
                     | (head11,args1) ->
                         let uu____12296 = FStar_Syntax_Util.head_and_args t2
                            in
                         (match uu____12296 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1  in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____12350 =
                                  let uu____12351 =
                                    FStar_Syntax_Print.term_to_string head11
                                     in
                                  let uu____12352 = args_to_string args1  in
                                  let uu____12353 =
                                    FStar_Syntax_Print.term_to_string head21
                                     in
                                  let uu____12354 = args_to_string args2  in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____12351 uu____12352 uu____12353
                                    uu____12354
                                   in
                                giveup env1 uu____12350 orig
                              else
                                (let uu____12356 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____12362 =
                                        FStar_Syntax_Util.eq_args args1 args2
                                         in
                                      uu____12362 = FStar_Syntax_Util.Equal)
                                    in
                                 if uu____12356
                                 then
                                   let uu____12363 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1
                                      in
                                   match uu____12363 with
                                   | USolved wl2 ->
                                       let uu____12365 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2
                                          in
                                       solve env1 uu____12365
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____12369 =
                                      base_and_refinement env1 t1  in
                                    match uu____12369 with
                                    | (base1,refinement1) ->
                                        let uu____12394 =
                                          base_and_refinement env1 t2  in
                                        (match uu____12394 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____12451 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1
                                                     in
                                                  (match uu____12451 with
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
                                                           (fun uu____12473 
                                                              ->
                                                              fun uu____12474
                                                                 ->
                                                                match 
                                                                  (uu____12473,
                                                                    uu____12474)
                                                                with
                                                                | ((a,uu____12492),
                                                                   (a',uu____12494))
                                                                    ->
                                                                    let uu____12503
                                                                    =
                                                                    mk_problem
                                                                    (p_scope
                                                                    orig)
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a'
                                                                    FStar_Pervasives_Native.None
                                                                    "index"
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    (fun
                                                                    _0_56  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_56)
                                                                    uu____12503)
                                                           args1 args2
                                                          in
                                                       let formula =
                                                         let uu____12513 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____12513
                                                          in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2
                                                          in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____12519 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1)
                                                     in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2)
                                                     in
                                                  solve_t env1
                                                    (let uu___144_12555 =
                                                       problem  in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___144_12555.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___144_12555.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___144_12555.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___144_12555.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___144_12555.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___144_12555.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___144_12555.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___144_12555.FStar_TypeChecker_Common.rank)
                                                     }) wl1))))))))
           in
        let force_quasi_pattern xs_opt uu____12588 =
          match uu____12588 with
          | (t,u,k,args) ->
              let debug1 f =
                let uu____12630 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12630 then f () else ()  in
              let rec aux pat_args pat_args_set pattern_vars pattern_var_set
                seen_formals formals res_t args1 =
                debug1
                  (fun uu____12726  ->
                     let uu____12727 =
                       FStar_Syntax_Print.binders_to_string ", " pat_args  in
                     FStar_Util.print1 "pat_args so far: {%s}\n" uu____12727);
                (match (formals, args1) with
                 | ([],[]) ->
                     let pat_args1 =
                       FStar_All.pipe_right (FStar_List.rev pat_args)
                         (FStar_List.map
                            (fun uu____12795  ->
                               match uu____12795 with
                               | (x,imp) ->
                                   let uu____12806 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   (uu____12806, imp)))
                        in
                     let pattern_vars1 = FStar_List.rev pattern_vars  in
                     let kk =
                       let uu____12819 = FStar_Syntax_Util.type_u ()  in
                       match uu____12819 with
                       | (t1,uu____12825) ->
                           let uu____12826 =
                             new_uvar t1.FStar_Syntax_Syntax.pos
                               pattern_vars1 t1
                              in
                           FStar_Pervasives_Native.fst uu____12826
                        in
                     let uu____12831 =
                       new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk
                        in
                     (match uu____12831 with
                      | (t',tm_u1) ->
                          let uu____12844 = destruct_flex_t t'  in
                          (match uu____12844 with
                           | (uu____12881,u1,k1,uu____12884) ->
                               let all_formals = FStar_List.rev seen_formals
                                  in
                               let k2 =
                                 let uu____12943 =
                                   FStar_Syntax_Syntax.mk_Total res_t  in
                                 FStar_Syntax_Util.arrow all_formals
                                   uu____12943
                                  in
                               let sol =
                                 let uu____12947 =
                                   let uu____12956 = u_abs k2 all_formals t'
                                      in
                                   ((u, k2), uu____12956)  in
                                 TERM uu____12947  in
                               let t_app =
                                 FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                   pat_args1 FStar_Pervasives_Native.None
                                   t.FStar_Syntax_Syntax.pos
                                  in
                               FStar_Pervasives_Native.Some
                                 (sol, (t_app, u1, k1, pat_args1))))
                 | (formal::formals1,hd1::tl1) ->
                     (debug1
                        (fun uu____13091  ->
                           let uu____13092 =
                             FStar_Syntax_Print.binder_to_string formal  in
                           let uu____13093 =
                             FStar_Syntax_Print.args_to_string [hd1]  in
                           FStar_Util.print2
                             "force_quasi_pattern (case 2): formal=%s, hd=%s\n"
                             uu____13092 uu____13093);
                      (let uu____13106 = pat_var_opt env pat_args hd1  in
                       match uu____13106 with
                       | FStar_Pervasives_Native.None  ->
                           (debug1
                              (fun uu____13126  ->
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
                                      (fun uu____13169  ->
                                         match uu____13169 with
                                         | (x,uu____13175) ->
                                             FStar_Syntax_Syntax.bv_eq x
                                               (FStar_Pervasives_Native.fst y)))
                              in
                           if Prims.op_Negation maybe_pat
                           then
                             aux pat_args pat_args_set pattern_vars
                               pattern_var_set (formal :: seen_formals)
                               formals1 res_t tl1
                           else
                             (debug1
                                (fun uu____13190  ->
                                   let uu____13191 =
                                     FStar_Syntax_Print.args_to_string [hd1]
                                      in
                                   let uu____13204 =
                                     FStar_Syntax_Print.binder_to_string y
                                      in
                                   FStar_Util.print2
                                     "%s (var = %s) maybe pat\n" uu____13191
                                     uu____13204);
                              (let fvs =
                                 FStar_Syntax_Free.names
                                   (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort
                                  in
                               let uu____13208 =
                                 let uu____13209 =
                                   FStar_Util.set_is_subset_of fvs
                                     pat_args_set
                                    in
                                 Prims.op_Negation uu____13209  in
                               if uu____13208
                               then
                                 (debug1
                                    (fun uu____13221  ->
                                       let uu____13222 =
                                         let uu____13225 =
                                           FStar_Syntax_Print.args_to_string
                                             [hd1]
                                            in
                                         let uu____13238 =
                                           let uu____13241 =
                                             FStar_Syntax_Print.binder_to_string
                                               y
                                              in
                                           let uu____13242 =
                                             let uu____13245 =
                                               FStar_Syntax_Print.term_to_string
                                                 (FStar_Pervasives_Native.fst
                                                    y).FStar_Syntax_Syntax.sort
                                                in
                                             let uu____13246 =
                                               let uu____13249 =
                                                 names_to_string fvs  in
                                               let uu____13250 =
                                                 let uu____13253 =
                                                   names_to_string
                                                     pattern_var_set
                                                    in
                                                 [uu____13253]  in
                                               uu____13249 :: uu____13250  in
                                             uu____13245 :: uu____13246  in
                                           uu____13241 :: uu____13242  in
                                         uu____13225 :: uu____13238  in
                                       FStar_Util.print
                                         "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n"
                                         uu____13222);
                                  aux pat_args pat_args_set pattern_vars
                                    pattern_var_set (formal :: seen_formals)
                                    formals1 res_t tl1)
                               else
                                 (let uu____13255 =
                                    FStar_Util.set_add
                                      (FStar_Pervasives_Native.fst y)
                                      pat_args_set
                                     in
                                  let uu____13258 =
                                    FStar_Util.set_add
                                      (FStar_Pervasives_Native.fst formal)
                                      pattern_var_set
                                     in
                                  aux (y :: pat_args) uu____13255 (formal ::
                                    pattern_vars) uu____13258 (formal ::
                                    seen_formals) formals1 res_t tl1)))))
                 | ([],uu____13265::uu____13266) ->
                     let uu____13297 =
                       let uu____13310 =
                         FStar_TypeChecker_Normalize.unfold_whnf env res_t
                          in
                       FStar_Syntax_Util.arrow_formals uu____13310  in
                     (match uu____13297 with
                      | (more_formals,res_t1) ->
                          (match more_formals with
                           | [] -> FStar_Pervasives_Native.None
                           | uu____13349 ->
                               aux pat_args pat_args_set pattern_vars
                                 pattern_var_set seen_formals more_formals
                                 res_t1 args1))
                 | (uu____13356::uu____13357,[]) ->
                     FStar_Pervasives_Native.None)
                 in
              let uu____13380 =
                let uu____13393 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k  in
                FStar_Syntax_Util.arrow_formals uu____13393  in
              (match uu____13380 with
               | (all_formals,res_t) ->
                   (debug1
                      (fun uu____13429  ->
                         let uu____13430 =
                           FStar_Syntax_Print.term_to_string t  in
                         let uu____13431 =
                           FStar_Syntax_Print.binders_to_string ", "
                             all_formals
                            in
                         let uu____13432 =
                           FStar_Syntax_Print.term_to_string res_t  in
                         let uu____13433 =
                           FStar_Syntax_Print.args_to_string args  in
                         FStar_Util.print4
                           "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n"
                           uu____13430 uu____13431 uu____13432 uu____13433);
                    (let uu____13434 = FStar_Syntax_Syntax.new_bv_set ()  in
                     let uu____13437 = FStar_Syntax_Syntax.new_bv_set ()  in
                     aux [] uu____13434 [] uu____13437 [] all_formals res_t
                       args)))
           in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____13471 = lhs  in
          match uu____13471 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____13481 ->
                    let uu____13482 = sn_binders env1 pat_vars1  in
                    u_abs k_uv uu____13482 rhs
                 in
              let wl2 =
                solve_prob orig FStar_Pervasives_Native.None
                  [TERM ((uv, k_uv), sol)] wl1
                 in
              solve env1 wl2
           in
        let imitate orig env1 wl1 p =
          let uu____13505 = p  in
          match uu____13505 with
          | (((u,k),xs,c),ps,(h,uu____13516,qs)) ->
              let xs1 = sn_binders env1 xs  in
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____13598 = imitation_sub_probs orig env1 xs1 ps qs  in
              (match uu____13598 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13621 = h gs_xs  in
                     let uu____13622 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57)
                        in
                     FStar_Syntax_Util.abs xs1 uu____13621 uu____13622  in
                   ((let uu____13628 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____13628
                     then
                       let uu____13629 =
                         let uu____13632 =
                           let uu____13633 =
                             FStar_List.map tc_to_string gs_xs  in
                           FStar_All.pipe_right uu____13633
                             (FStar_String.concat "\n\t>")
                            in
                         let uu____13638 =
                           let uu____13641 =
                             FStar_Syntax_Print.binders_to_string ", " xs1
                              in
                           let uu____13642 =
                             let uu____13645 =
                               FStar_Syntax_Print.comp_to_string c  in
                             let uu____13646 =
                               let uu____13649 =
                                 FStar_Syntax_Print.term_to_string im  in
                               let uu____13650 =
                                 let uu____13653 =
                                   FStar_Syntax_Print.tag_of_term im  in
                                 let uu____13654 =
                                   let uu____13657 =
                                     let uu____13658 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs
                                        in
                                     FStar_All.pipe_right uu____13658
                                       (FStar_String.concat ", ")
                                      in
                                   let uu____13663 =
                                     let uu____13666 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula
                                        in
                                     [uu____13666]  in
                                   uu____13657 :: uu____13663  in
                                 uu____13653 :: uu____13654  in
                               uu____13649 :: uu____13650  in
                             uu____13645 :: uu____13646  in
                           uu____13641 :: uu____13642  in
                         uu____13632 :: uu____13638  in
                       FStar_Util.print
                         "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13629
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1
                        in
                     solve env1 (attempt sub_probs wl2))))
           in
        let imitate' orig env1 wl1 uu___108_13687 =
          match uu___108_13687 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p  in
        let project orig env1 wl1 i p =
          let uu____13719 = p  in
          match uu____13719 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____13810 = FStar_List.nth ps i  in
              (match uu____13810 with
               | (pi,uu____13814) ->
                   let uu____13819 = FStar_List.nth xs i  in
                   (match uu____13819 with
                    | (xi,uu____13831) ->
                        let rec gs k =
                          let uu____13844 =
                            let uu____13857 =
                              FStar_TypeChecker_Normalize.unfold_whnf env1 k
                               in
                            FStar_Syntax_Util.arrow_formals uu____13857  in
                          match uu____13844 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____13932)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort
                                       in
                                    let uu____13945 = new_uvar r xs k_a  in
                                    (match uu____13945 with
                                     | (gi_xs,gi) ->
                                         let gi_xs1 =
                                           FStar_TypeChecker_Normalize.eta_expand
                                             env1 gi_xs
                                            in
                                         let gi_ps =
                                           FStar_Syntax_Syntax.mk_Tm_app gi
                                             ps FStar_Pervasives_Native.None
                                             r
                                            in
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT
                                              (a, gi_xs1))
                                           :: subst1  in
                                         let uu____13967 = aux subst2 tl1  in
                                         (match uu____13967 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____13994 =
                                                let uu____13997 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1
                                                   in
                                                uu____13997 :: gi_xs'  in
                                              let uu____13998 =
                                                let uu____14001 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps
                                                   in
                                                uu____14001 :: gi_ps'  in
                                              (uu____13994, uu____13998)))
                                 in
                              aux [] bs
                           in
                        let uu____14006 =
                          let uu____14007 = matches pi  in
                          FStar_All.pipe_left Prims.op_Negation uu____14007
                           in
                        if uu____14006
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____14011 = gs xi.FStar_Syntax_Syntax.sort
                              in
                           match uu____14011 with
                           | (g_xs,uu____14023) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                  in
                               let proj =
                                 let uu____14034 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r
                                    in
                                 let uu____14035 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_58  ->
                                        FStar_Pervasives_Native.Some _0_58)
                                    in
                                 FStar_Syntax_Util.abs xs uu____14034
                                   uu____14035
                                  in
                               let sub1 =
                                 let uu____14041 =
                                   let uu____14046 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r
                                      in
                                   let uu____14049 =
                                     let uu____14052 =
                                       FStar_List.map
                                         (fun uu____14067  ->
                                            match uu____14067 with
                                            | (uu____14076,uu____14077,y) ->
                                                y) qs
                                        in
                                     FStar_All.pipe_left h uu____14052  in
                                   mk_problem (p_scope orig) orig uu____14046
                                     (p_rel orig) uu____14049
                                     FStar_Pervasives_Native.None
                                     "projection"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____14041
                                  in
                               ((let uu____14092 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____14092
                                 then
                                   let uu____14093 =
                                     FStar_Syntax_Print.term_to_string proj
                                      in
                                   let uu____14094 = prob_to_string env1 sub1
                                      in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____14093 uu____14094
                                 else ());
                                (let wl2 =
                                   let uu____14097 =
                                     let uu____14100 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1)
                                        in
                                     FStar_Pervasives_Native.Some uu____14100
                                      in
                                   solve_prob orig uu____14097
                                     [TERM (u, proj)] wl1
                                    in
                                 let uu____14109 =
                                   solve env1 (attempt [sub1] wl2)  in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____14109)))))
           in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____14140 = lhs  in
          match uu____14140 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____14176 = FStar_Syntax_Util.arrow_formals_comp k_uv
                   in
                match uu____14176 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____14209 =
                        let uu____14256 = decompose env t2  in
                        (((uv, k_uv), xs, c), ps, uu____14256)  in
                      FStar_Pervasives_Native.Some uu____14209
                    else
                      (let rec elim k args =
                         let k1 =
                           FStar_TypeChecker_Normalize.unfold_whnf env k  in
                         let uu____14400 =
                           let uu____14407 =
                             let uu____14408 = FStar_Syntax_Subst.compress k1
                                in
                             uu____14408.FStar_Syntax_Syntax.n  in
                           (uu____14407, args)  in
                         match uu____14400 with
                         | (uu____14419,[]) ->
                             let uu____14422 =
                               let uu____14433 =
                                 FStar_Syntax_Syntax.mk_Total k1  in
                               ([], uu____14433)  in
                             FStar_Pervasives_Native.Some uu____14422
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____14454,uu____14455) ->
                             let uu____14476 =
                               FStar_Syntax_Util.head_and_args k1  in
                             (match uu____14476 with
                              | (uv1,uv_args) ->
                                  let uu____14519 =
                                    let uu____14520 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____14520.FStar_Syntax_Syntax.n  in
                                  (match uu____14519 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14530) ->
                                       let uu____14555 =
                                         pat_vars env [] uv_args  in
                                       (match uu____14555 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14582  ->
                                                      let uu____14583 =
                                                        let uu____14584 =
                                                          let uu____14585 =
                                                            let uu____14590 =
                                                              let uu____14591
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____14591
                                                                FStar_Pervasives_Native.fst
                                                               in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14590
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14585
                                                           in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14584
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14583))
                                               in
                                            let c1 =
                                              let uu____14601 =
                                                let uu____14602 =
                                                  let uu____14607 =
                                                    let uu____14608 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____14608
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14607
                                                   in
                                                FStar_Pervasives_Native.fst
                                                  uu____14602
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14601
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____14621 =
                                                let uu____14624 =
                                                  let uu____14625 =
                                                    let uu____14628 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____14628
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14625
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____14624
                                                 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14621
                                               in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14646 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14651,uu____14652) ->
                             let uu____14671 =
                               FStar_Syntax_Util.head_and_args k1  in
                             (match uu____14671 with
                              | (uv1,uv_args) ->
                                  let uu____14714 =
                                    let uu____14715 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____14715.FStar_Syntax_Syntax.n  in
                                  (match uu____14714 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14725) ->
                                       let uu____14750 =
                                         pat_vars env [] uv_args  in
                                       (match uu____14750 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14777  ->
                                                      let uu____14778 =
                                                        let uu____14779 =
                                                          let uu____14780 =
                                                            let uu____14785 =
                                                              let uu____14786
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____14786
                                                                FStar_Pervasives_Native.fst
                                                               in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14785
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14780
                                                           in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14779
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14778))
                                               in
                                            let c1 =
                                              let uu____14796 =
                                                let uu____14797 =
                                                  let uu____14802 =
                                                    let uu____14803 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____14803
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14802
                                                   in
                                                FStar_Pervasives_Native.fst
                                                  uu____14797
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14796
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____14816 =
                                                let uu____14819 =
                                                  let uu____14820 =
                                                    let uu____14823 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____14823
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14820
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____14819
                                                 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14816
                                               in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14841 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____14848) ->
                             let n_args = FStar_List.length args  in
                             let n_xs = FStar_List.length xs1  in
                             if n_xs = n_args
                             then
                               let uu____14889 =
                                 FStar_Syntax_Subst.open_comp xs1 c1  in
                               FStar_All.pipe_right uu____14889
                                 (fun _0_61  ->
                                    FStar_Pervasives_Native.Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____14925 =
                                    FStar_Util.first_N n_xs args  in
                                  match uu____14925 with
                                  | (args1,rest) ->
                                      let uu____14954 =
                                        FStar_Syntax_Subst.open_comp xs1 c1
                                         in
                                      (match uu____14954 with
                                       | (xs2,c2) ->
                                           let uu____14967 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest
                                              in
                                           FStar_Util.bind_opt uu____14967
                                             (fun uu____14991  ->
                                                match uu____14991 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____15031 =
                                    FStar_Util.first_N n_args xs1  in
                                  match uu____15031 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k1.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____15099 =
                                        let uu____15104 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____15104
                                         in
                                      FStar_All.pipe_right uu____15099
                                        (fun _0_62  ->
                                           FStar_Pervasives_Native.Some _0_62))
                         | uu____15119 ->
                             let uu____15126 =
                               let uu____15131 =
                                 let uu____15132 =
                                   FStar_Syntax_Print.uvar_to_string uv  in
                                 let uu____15133 =
                                   FStar_Syntax_Print.term_to_string k1  in
                                 let uu____15134 =
                                   FStar_Syntax_Print.term_to_string k_uv  in
                                 FStar_Util.format3
                                   "Impossible: ill-typed application %s : %s\n\t%s"
                                   uu____15132 uu____15133 uu____15134
                                  in
                               (FStar_Errors.Fatal_IllTyped, uu____15131)  in
                             FStar_Errors.raise_error uu____15126
                               t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15141 = elim k_uv ps  in
                       FStar_Util.bind_opt uu____15141
                         (fun uu____15196  ->
                            match uu____15196 with
                            | (xs1,c1) ->
                                let uu____15245 =
                                  let uu____15286 = decompose env t2  in
                                  (((uv, k_uv), xs1, c1), ps, uu____15286)
                                   in
                                FStar_Pervasives_Native.Some uu____15245))
                 in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail uu____15407 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig
                   in
                let rec try_project st i =
                  if i >= n1
                  then fail ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                     let uu____15421 = project orig env wl1 i st  in
                     match uu____15421 with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some (Failed uu____15435) ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some sol -> sol)
                   in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt  in
                  let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                  let uu____15450 = imitate orig env wl1 st  in
                  match uu____15450 with
                  | Failed uu____15455 ->
                      (FStar_Syntax_Unionfind.rollback tx;
                       try_project st (Prims.parse_int "0"))
                  | sol -> sol
                else fail ()  in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____15486 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1  in
                match uu____15486 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let uu____15509 = forced_lhs_pattern  in
                    (match uu____15509 with
                     | (lhs_t,uu____15511,uu____15512,uu____15513) ->
                         ((let uu____15515 =
                             FStar_TypeChecker_Env.debug env
                               (FStar_Options.Other "Rel")
                              in
                           if uu____15515
                           then
                             let uu____15516 = lhs1  in
                             match uu____15516 with
                             | (t0,uu____15518,uu____15519,uu____15520) ->
                                 let uu____15521 = forced_lhs_pattern  in
                                 (match uu____15521 with
                                  | (t11,uu____15523,uu____15524,uu____15525)
                                      ->
                                      let uu____15526 =
                                        FStar_Syntax_Print.term_to_string t0
                                         in
                                      let uu____15527 =
                                        FStar_Syntax_Print.term_to_string t11
                                         in
                                      FStar_Util.print2
                                        "force_quasi_pattern succeeded, turning %s into %s\n"
                                        uu____15526 uu____15527)
                           else ());
                          (let rhs_vars = FStar_Syntax_Free.names rhs  in
                           let lhs_vars = FStar_Syntax_Free.names lhs_t  in
                           let uu____15535 =
                             FStar_Util.set_is_subset_of rhs_vars lhs_vars
                              in
                           if uu____15535
                           then
                             ((let uu____15537 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "Rel")
                                  in
                               if uu____15537
                               then
                                 let uu____15538 =
                                   FStar_Syntax_Print.term_to_string rhs  in
                                 let uu____15539 = names_to_string rhs_vars
                                    in
                                 let uu____15540 = names_to_string lhs_vars
                                    in
                                 FStar_Util.print3
                                   "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n"
                                   uu____15538 uu____15539 uu____15540
                               else ());
                              (let tx =
                                 FStar_Syntax_Unionfind.new_transaction ()
                                  in
                               let wl2 =
                                 extend_solution (p_pid orig) [sol] wl1  in
                               let uu____15544 =
                                 let uu____15545 =
                                   FStar_TypeChecker_Common.as_tprob orig  in
                                 solve_t env uu____15545 wl2  in
                               match uu____15544 with
                               | Failed uu____15546 ->
                                   (FStar_Syntax_Unionfind.rollback tx;
                                    imitate_or_project n1 lhs1 rhs stopt)
                               | sol1 -> sol1))
                           else
                             ((let uu____15555 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "Rel")
                                  in
                               if uu____15555
                               then
                                 FStar_Util.print_string
                                   "fvar check failed for quasi pattern ... im/proj\n"
                               else ());
                              imitate_or_project n1 lhs1 rhs stopt))))
                 in
              let check_head fvs1 t21 =
                let uu____15568 = FStar_Syntax_Util.head_and_args t21  in
                match uu____15568 with
                | (hd1,uu____15584) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15605 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15618 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15619 -> true
                     | uu____15636 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1  in
                         let uu____15640 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1  in
                         if uu____15640
                         then true
                         else
                           ((let uu____15643 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____15643
                             then
                               let uu____15644 = names_to_string fvs_hd  in
                               FStar_Util.print1 "Free variables are %s\n"
                                 uu____15644
                             else ());
                            false))
                 in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1  in
                   let t21 = sn env t2  in
                   let lhs1 = (t11, uv, k_uv, args_lhs)  in
                   let fvs1 = FStar_Syntax_Free.names t11  in
                   let fvs2 = FStar_Syntax_Free.names t21  in
                   let uu____15664 = occurs_check env wl1 (uv, k_uv) t21  in
                   (match uu____15664 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15677 =
                            let uu____15678 = FStar_Option.get msg  in
                            Prims.strcat "occurs-check failed: " uu____15678
                             in
                          giveup_or_defer1 orig uu____15677
                        else
                          (let uu____15680 =
                             FStar_Util.set_is_subset_of fvs2 fvs1  in
                           if uu____15680
                           then
                             let uu____15681 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
                                in
                             (if uu____15681
                              then
                                let uu____15682 = subterms args_lhs  in
                                imitate' orig env wl1 uu____15682
                              else
                                ((let uu____15687 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____15687
                                  then
                                    let uu____15688 =
                                      FStar_Syntax_Print.term_to_string t11
                                       in
                                    let uu____15689 = names_to_string fvs1
                                       in
                                    let uu____15690 = names_to_string fvs2
                                       in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15688 uu____15689 uu____15690
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
                               (let uu____15694 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21)
                                   in
                                if uu____15694
                                then
                                  ((let uu____15696 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____15696
                                    then
                                      let uu____15697 =
                                        FStar_Syntax_Print.term_to_string t11
                                         in
                                      let uu____15698 = names_to_string fvs1
                                         in
                                      let uu____15699 = names_to_string fvs2
                                         in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                        uu____15697 uu____15698 uu____15699
                                    else ());
                                   (let uu____15701 = subterms args_lhs  in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) lhs1 t21
                                      uu____15701))
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
                     (let uu____15712 =
                        let uu____15713 = FStar_Syntax_Free.names t1  in
                        check_head uu____15713 t2  in
                      if uu____15712
                      then
                        let n_args_lhs = FStar_List.length args_lhs  in
                        ((let uu____15724 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel")
                             in
                          if uu____15724
                          then
                            let uu____15725 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____15726 =
                              FStar_Util.string_of_int n_args_lhs  in
                            FStar_Util.print2
                              "Not a pattern (%s) ... (lhs has %s args)\n"
                              uu____15725 uu____15726
                          else ());
                         (let uu____15734 = subterms args_lhs  in
                          pattern_eq_imitate_or_project n_args_lhs
                            (FStar_Pervasives_Native.fst lhs) t2 uu____15734))
                      else giveup env "head-symbol is free" orig))
           in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let solve_both_pats wl1 uu____15811 uu____15812 r =
               match (uu____15811, uu____15812) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____16010 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys)
                      in
                   if uu____16010
                   then
                     let uu____16011 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1
                        in
                     solve env uu____16011
                   else
                     (let xs1 = sn_binders env xs  in
                      let ys1 = sn_binders env ys  in
                      let zs = intersect_vars xs1 ys1  in
                      (let uu____16035 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____16035
                       then
                         let uu____16036 =
                           FStar_Syntax_Print.binders_to_string ", " xs1  in
                         let uu____16037 =
                           FStar_Syntax_Print.binders_to_string ", " ys1  in
                         let uu____16038 =
                           FStar_Syntax_Print.binders_to_string ", " zs  in
                         let uu____16039 =
                           FStar_Syntax_Print.term_to_string k1  in
                         let uu____16040 =
                           FStar_Syntax_Print.term_to_string k2  in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____16036 uu____16037 uu____16038 uu____16039
                           uu____16040
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2  in
                         let args_len = FStar_List.length args  in
                         if xs_len = args_len
                         then
                           let uu____16100 =
                             FStar_Syntax_Util.subst_of_list xs2 args  in
                           FStar_Syntax_Subst.subst uu____16100 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____16114 =
                                FStar_Util.first_N args_len xs2  in
                              match uu____16114 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____16168 =
                                      FStar_Syntax_Syntax.mk_GTotal k  in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____16168
                                     in
                                  let uu____16171 =
                                    FStar_Syntax_Util.subst_of_list xs3 args
                                     in
                                  FStar_Syntax_Subst.subst uu____16171 k3)
                           else
                             (let uu____16175 =
                                let uu____16176 =
                                  FStar_Syntax_Print.term_to_string k  in
                                let uu____16177 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2
                                   in
                                let uu____16178 =
                                  FStar_Syntax_Print.args_to_string args  in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____16176 uu____16177 uu____16178
                                 in
                              failwith uu____16175)
                          in
                       let uu____16179 =
                         let uu____16186 =
                           let uu____16199 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1
                              in
                           FStar_Syntax_Util.arrow_formals uu____16199  in
                         match uu____16186 with
                         | (bs,k1') ->
                             let uu____16224 =
                               let uu____16237 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2
                                  in
                               FStar_Syntax_Util.arrow_formals uu____16237
                                in
                             (match uu____16224 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1  in
                                  let k2'_ys = subst_k k2' cs args2  in
                                  let sub_prob =
                                    let uu____16265 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____16265
                                     in
                                  let uu____16274 =
                                    let uu____16279 =
                                      let uu____16280 =
                                        FStar_Syntax_Subst.compress k1'  in
                                      uu____16280.FStar_Syntax_Syntax.n  in
                                    let uu____16283 =
                                      let uu____16284 =
                                        FStar_Syntax_Subst.compress k2'  in
                                      uu____16284.FStar_Syntax_Syntax.n  in
                                    (uu____16279, uu____16283)  in
                                  (match uu____16274 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____16293,uu____16294) ->
                                       (k1'_xs, [sub_prob])
                                   | (uu____16297,FStar_Syntax_Syntax.Tm_type
                                      uu____16298) -> (k2'_ys, [sub_prob])
                                   | uu____16301 ->
                                       let uu____16306 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____16306 with
                                        | (t,uu____16318) ->
                                            let uu____16319 = new_uvar r zs t
                                               in
                                            (match uu____16319 with
                                             | (k_zs,uu____16331) ->
                                                 let kprob =
                                                   let uu____16333 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs
                                                       FStar_Pervasives_Native.None
                                                       "flex-flex kinding"
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_64  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_64) uu____16333
                                                    in
                                                 (k_zs, [sub_prob; kprob])))))
                          in
                       match uu____16179 with
                       | (k_u',sub_probs) ->
                           let uu____16350 =
                             let uu____16361 =
                               let uu____16362 = new_uvar r zs k_u'  in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____16362
                                in
                             let uu____16371 =
                               let uu____16374 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow xs1 uu____16374  in
                             let uu____16377 =
                               let uu____16380 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow ys1 uu____16380  in
                             (uu____16361, uu____16371, uu____16377)  in
                           (match uu____16350 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs  in
                                let uu____16399 =
                                  occurs_check env wl1 (u1, k1) sub1  in
                                (match uu____16399 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1)  in
                                        let uu____16418 =
                                          FStar_Syntax_Unionfind.equiv u1 u2
                                           in
                                        if uu____16418
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1
                                             in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs
                                              in
                                           let uu____16422 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2
                                              in
                                           match uu____16422 with
                                           | (occurs_ok1,msg1) ->
                                               if
                                                 Prims.op_Negation occurs_ok1
                                               then
                                                 giveup_or_defer1 orig
                                                   "flex-flex: failed occurs check"
                                               else
                                                 (let sol2 =
                                                    TERM ((u2, k2), sub2)  in
                                                  let wl2 =
                                                    solve_prob orig
                                                      FStar_Pervasives_Native.None
                                                      [sol1; sol2] wl1
                                                     in
                                                  solve env
                                                    (attempt sub_probs wl2))))))))
                in
             let solve_one_pat uu____16475 uu____16476 =
               match (uu____16475, uu____16476) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____16594 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____16594
                     then
                       let uu____16595 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____16596 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____16595 uu____16596
                     else ());
                    (let uu____16598 = FStar_Syntax_Unionfind.equiv u1 u2  in
                     if uu____16598
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16617  ->
                              fun uu____16618  ->
                                match (uu____16617, uu____16618) with
                                | ((a,uu____16636),(t21,uu____16638)) ->
                                    let uu____16647 =
                                      let uu____16652 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      mk_problem (p_scope orig) orig
                                        uu____16652
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index"
                                       in
                                    FStar_All.pipe_right uu____16647
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2
                          in
                       let guard =
                         let uu____16658 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____16658  in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl
                          in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2  in
                        let rhs_vars = FStar_Syntax_Free.names t21  in
                        let uu____16673 = occurs_check env wl (u1, k1) t21
                           in
                        match uu____16673 with
                        | (occurs_ok,uu____16681) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs  in
                            let uu____16689 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars)
                               in
                            if uu____16689
                            then
                              let sol =
                                let uu____16691 =
                                  let uu____16700 = u_abs k1 xs t21  in
                                  ((u1, k1), uu____16700)  in
                                TERM uu____16691  in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl
                                 in
                              solve env wl1
                            else
                              (let uu____16707 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok)
                                  in
                               if uu____16707
                               then
                                 let uu____16708 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2)
                                    in
                                 match uu____16708 with
                                 | FStar_Pervasives_Native.None  ->
                                     giveup_or_defer1 orig
                                       "flex-flex constraint"
                                 | FStar_Pervasives_Native.Some
                                     (sol,(uu____16732,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl
                                        in
                                     ((let uu____16758 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern")
                                          in
                                       if uu____16758
                                       then
                                         let uu____16759 =
                                           uvi_to_string env sol  in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16759
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16766 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint"))))
                in
             let uu____16768 = lhs  in
             match uu____16768 with
             | (t1,u1,k1,args1) ->
                 let uu____16773 = rhs  in
                 (match uu____16773 with
                  | (t2,u2,k2,args2) ->
                      let maybe_pat_vars1 = pat_vars env [] args1  in
                      let maybe_pat_vars2 = pat_vars env [] args2  in
                      let r = t2.FStar_Syntax_Syntax.pos  in
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
                       | uu____16813 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16823 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1)
                                 in
                              match uu____16823 with
                              | FStar_Pervasives_Native.None  ->
                                  giveup env
                                    "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                    orig
                              | FStar_Pervasives_Native.Some
                                  (sol,uu____16841) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl  in
                                  ((let uu____16848 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern")
                                       in
                                    if uu____16848
                                    then
                                      let uu____16849 = uvi_to_string env sol
                                         in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16849
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16856 ->
                                        giveup env "impossible" orig))))))
           in
        let orig = FStar_TypeChecker_Common.TProb problem  in
        let uu____16858 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs
           in
        if uu____16858
        then
          let uu____16859 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____16859
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs  in
           let t2 = problem.FStar_TypeChecker_Common.rhs  in
           let uu____16863 = FStar_Util.physical_equality t1 t2  in
           if uu____16863
           then
             let uu____16864 =
               solve_prob orig FStar_Pervasives_Native.None [] wl  in
             solve env uu____16864
           else
             ((let uu____16867 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck")
                  in
               if uu____16867
               then
                 let uu____16868 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid
                    in
                 FStar_Util.print1 "Attempting %s\n" uu____16868
               else ());
              (let r = FStar_TypeChecker_Env.get_range env  in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_ascribed uu____16871,uu____16872) ->
                   let uu____16899 =
                     let uu___145_16900 = problem  in
                     let uu____16901 = FStar_Syntax_Util.unmeta t1  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___145_16900.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16901;
                       FStar_TypeChecker_Common.relation =
                         (uu___145_16900.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___145_16900.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___145_16900.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___145_16900.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___145_16900.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___145_16900.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___145_16900.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___145_16900.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____16899 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____16902,uu____16903) ->
                   let uu____16910 =
                     let uu___145_16911 = problem  in
                     let uu____16912 = FStar_Syntax_Util.unmeta t1  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___145_16911.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16912;
                       FStar_TypeChecker_Common.relation =
                         (uu___145_16911.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___145_16911.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___145_16911.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___145_16911.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___145_16911.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___145_16911.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___145_16911.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___145_16911.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____16910 wl
               | (uu____16913,FStar_Syntax_Syntax.Tm_ascribed uu____16914) ->
                   let uu____16941 =
                     let uu___146_16942 = problem  in
                     let uu____16943 = FStar_Syntax_Util.unmeta t2  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___146_16942.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___146_16942.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___146_16942.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16943;
                       FStar_TypeChecker_Common.element =
                         (uu___146_16942.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___146_16942.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___146_16942.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___146_16942.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___146_16942.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___146_16942.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____16941 wl
               | (uu____16944,FStar_Syntax_Syntax.Tm_meta uu____16945) ->
                   let uu____16952 =
                     let uu___146_16953 = problem  in
                     let uu____16954 = FStar_Syntax_Util.unmeta t2  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___146_16953.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___146_16953.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___146_16953.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16954;
                       FStar_TypeChecker_Common.element =
                         (uu___146_16953.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___146_16953.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___146_16953.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___146_16953.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___146_16953.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___146_16953.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____16952 wl
               | (FStar_Syntax_Syntax.Tm_bvar uu____16955,uu____16956) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____16957,FStar_Syntax_Syntax.Tm_bvar uu____16958) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___109_17013 =
                     match uu___109_17013 with
                     | [] -> c
                     | bs ->
                         let uu____17035 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos
                            in
                         FStar_Syntax_Syntax.mk_Total uu____17035
                      in
                   let uu____17044 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                   (match uu____17044 with
                    | ((bs11,c11),(bs21,c21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let c12 =
                                   FStar_Syntax_Subst.subst_comp subst1 c11
                                    in
                                 let c22 =
                                   FStar_Syntax_Subst.subst_comp subst1 c21
                                    in
                                 let rel =
                                   let uu____17186 =
                                     FStar_Options.use_eq_at_higher_order ()
                                      in
                                   if uu____17186
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation
                                    in
                                 let uu____17188 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____17188))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___110_17264 =
                     match uu___110_17264 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos
                      in
                   let uu____17298 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2))
                      in
                   (match uu____17298 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____17434 =
                                   let uu____17439 =
                                     FStar_Syntax_Subst.subst subst1 tbody11
                                      in
                                   let uu____17440 =
                                     FStar_Syntax_Subst.subst subst1 tbody21
                                      in
                                   mk_problem scope orig uu____17439
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____17440 FStar_Pervasives_Native.None
                                     "lambda co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____17434))
               | (FStar_Syntax_Syntax.Tm_abs uu____17445,uu____17446) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17471 -> true
                     | uu____17488 -> false  in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t
                           in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3)
                      in
                   let force_eta t =
                     if is_abs t
                     then t
                     else
                       (let uu____17535 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___147_17543 = env  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___147_17543.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___147_17543.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___147_17543.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___147_17543.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___147_17543.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___147_17543.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___147_17543.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___147_17543.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___147_17543.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___147_17543.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___147_17543.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___147_17543.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___147_17543.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___147_17543.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___147_17543.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___147_17543.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___147_17543.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___147_17543.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___147_17543.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___147_17543.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___147_17543.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___147_17543.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___147_17543.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___147_17543.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___147_17543.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___147_17543.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___147_17543.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___147_17543.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___147_17543.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___147_17543.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___147_17543.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___147_17543.FStar_TypeChecker_Env.dep_graph)
                             }) t
                           in
                        match uu____17535 with
                        | (uu____17546,ty,uu____17548) ->
                            let uu____17549 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty
                               in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17549)
                      in
                   let uu____17550 =
                     let uu____17567 = maybe_eta t1  in
                     let uu____17574 = maybe_eta t2  in
                     (uu____17567, uu____17574)  in
                   (match uu____17550 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___148_17616 = problem  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___148_17616.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___148_17616.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___148_17616.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___148_17616.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___148_17616.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___148_17616.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___148_17616.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___148_17616.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17639 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____17639
                        then
                          let uu____17640 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____17640 t_abs wl
                        else
                          (let t11 = force_eta t1  in
                           let t21 = force_eta t2  in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___149_17655 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___149_17655.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___149_17655.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___149_17655.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___149_17655.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___149_17655.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___149_17655.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___149_17655.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___149_17655.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17679 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____17679
                        then
                          let uu____17680 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____17680 t_abs wl
                        else
                          (let t11 = force_eta t1  in
                           let t21 = force_eta t2  in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___149_17695 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___149_17695.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___149_17695.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___149_17695.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___149_17695.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___149_17695.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___149_17695.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___149_17695.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___149_17695.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17699 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17716,FStar_Syntax_Syntax.Tm_abs uu____17717) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17742 -> true
                     | uu____17759 -> false  in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t3 =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t
                           in
                        if is_abs t3
                        then FStar_Util.Inl t3
                        else FStar_Util.Inr t3)
                      in
                   let force_eta t =
                     if is_abs t
                     then t
                     else
                       (let uu____17806 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___147_17814 = env  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___147_17814.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___147_17814.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___147_17814.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___147_17814.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___147_17814.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___147_17814.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___147_17814.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___147_17814.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___147_17814.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___147_17814.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___147_17814.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___147_17814.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___147_17814.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___147_17814.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___147_17814.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___147_17814.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___147_17814.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___147_17814.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___147_17814.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___147_17814.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___147_17814.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___147_17814.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___147_17814.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___147_17814.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___147_17814.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___147_17814.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___147_17814.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___147_17814.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___147_17814.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___147_17814.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___147_17814.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___147_17814.FStar_TypeChecker_Env.dep_graph)
                             }) t
                           in
                        match uu____17806 with
                        | (uu____17817,ty,uu____17819) ->
                            let uu____17820 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty
                               in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17820)
                      in
                   let uu____17821 =
                     let uu____17838 = maybe_eta t1  in
                     let uu____17845 = maybe_eta t2  in
                     (uu____17838, uu____17845)  in
                   (match uu____17821 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___148_17887 = problem  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___148_17887.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___148_17887.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___148_17887.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___148_17887.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___148_17887.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___148_17887.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___148_17887.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___148_17887.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17910 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____17910
                        then
                          let uu____17911 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____17911 t_abs wl
                        else
                          (let t11 = force_eta t1  in
                           let t21 = force_eta t2  in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___149_17926 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___149_17926.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___149_17926.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___149_17926.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___149_17926.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___149_17926.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___149_17926.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___149_17926.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___149_17926.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17950 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____17950
                        then
                          let uu____17951 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____17951 t_abs wl
                        else
                          (let t11 = force_eta t1  in
                           let t21 = force_eta t2  in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___149_17966 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___149_17966.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___149_17966.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___149_17966.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___149_17966.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___149_17966.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___149_17966.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___149_17966.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___149_17966.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17970 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                   let should_delta =
                     ((let uu____18002 = FStar_Syntax_Free.uvars t1  in
                       FStar_Util.set_is_empty uu____18002) &&
                        (let uu____18014 = FStar_Syntax_Free.uvars t2  in
                         FStar_Util.set_is_empty uu____18014))
                       &&
                       (let uu____18029 =
                          head_matches env x1.FStar_Syntax_Syntax.sort
                            x2.FStar_Syntax_Syntax.sort
                           in
                        match uu____18029 with
                        | MisMatch
                            (FStar_Pervasives_Native.Some
                             d1,FStar_Pervasives_Native.Some d2)
                            ->
                            let is_unfoldable uu___111_18039 =
                              match uu___111_18039 with
                              | FStar_Syntax_Syntax.Delta_constant  -> true
                              | FStar_Syntax_Syntax.Delta_defined_at_level
                                  uu____18040 -> true
                              | uu____18041 -> false  in
                            (is_unfoldable d1) && (is_unfoldable d2)
                        | uu____18042 -> false)
                      in
                   let uu____18043 = as_refinement should_delta env wl t1  in
                   (match uu____18043 with
                    | (x11,phi1) ->
                        let uu____18050 =
                          as_refinement should_delta env wl t2  in
                        (match uu____18050 with
                         | (x21,phi21) ->
                             let base_prob =
                               let uu____18058 =
                                 mk_problem (p_scope orig) orig
                                   x11.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x21.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____18058
                                in
                             let x12 = FStar_Syntax_Syntax.freshen_bv x11  in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x12)]
                                in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1
                                in
                             let phi22 =
                               FStar_Syntax_Subst.subst subst1 phi21  in
                             let env1 = FStar_TypeChecker_Env.push_bv env x12
                                in
                             let mk_imp1 imp phi12 phi23 =
                               let uu____18096 = imp phi12 phi23  in
                               FStar_All.pipe_right uu____18096
                                 (guard_on_element wl problem x12)
                                in
                             let fallback uu____18100 =
                               let impl =
                                 if
                                   problem.FStar_TypeChecker_Common.relation
                                     = FStar_TypeChecker_Common.EQ
                                 then
                                   mk_imp1 FStar_Syntax_Util.mk_iff phi11
                                     phi22
                                 else
                                   mk_imp1 FStar_Syntax_Util.mk_imp phi11
                                     phi22
                                  in
                               let guard =
                                 let uu____18106 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____18106 impl
                                  in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl
                                  in
                               solve env1 (attempt [base_prob] wl1)  in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____18115 =
                                   let uu____18120 =
                                     let uu____18121 =
                                       let uu____18128 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____18128]  in
                                     FStar_List.append (p_scope orig)
                                       uu____18121
                                      in
                                   mk_problem uu____18120 orig phi11
                                     FStar_TypeChecker_Common.EQ phi22
                                     FStar_Pervasives_Native.None
                                     "refinement formula"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____18115
                                  in
                               let uu____18137 =
                                 solve env1
                                   (let uu___150_18139 = wl  in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___150_18139.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___150_18139.smt_ok);
                                      tcenv = (uu___150_18139.tcenv)
                                    })
                                  in
                               (match uu____18137 with
                                | Failed uu____18146 -> fallback ()
                                | Success uu____18151 ->
                                    let guard =
                                      let uu____18155 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      let uu____18160 =
                                        let uu____18161 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____18161
                                          (guard_on_element wl problem x12)
                                         in
                                      FStar_Syntax_Util.mk_conj uu____18155
                                        uu____18160
                                       in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl
                                       in
                                    let wl2 =
                                      let uu___151_18170 = wl1  in
                                      {
                                        attempting =
                                          (uu___151_18170.attempting);
                                        wl_deferred =
                                          (uu___151_18170.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___151_18170.defer_ok);
                                        smt_ok = (uu___151_18170.smt_ok);
                                        tcenv = (uu___151_18170.tcenv)
                                      }  in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18172,FStar_Syntax_Syntax.Tm_uvar uu____18173) ->
                   let uu____18206 = destruct_flex_t t1  in
                   let uu____18207 = destruct_flex_t t2  in
                   flex_flex1 orig uu____18206 uu____18207
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18208;
                     FStar_Syntax_Syntax.pos = uu____18209;
                     FStar_Syntax_Syntax.vars = uu____18210;_},uu____18211),FStar_Syntax_Syntax.Tm_uvar
                  uu____18212) ->
                   let uu____18265 = destruct_flex_t t1  in
                   let uu____18266 = destruct_flex_t t2  in
                   flex_flex1 orig uu____18265 uu____18266
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18267,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18268;
                     FStar_Syntax_Syntax.pos = uu____18269;
                     FStar_Syntax_Syntax.vars = uu____18270;_},uu____18271))
                   ->
                   let uu____18324 = destruct_flex_t t1  in
                   let uu____18325 = destruct_flex_t t2  in
                   flex_flex1 orig uu____18324 uu____18325
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18326;
                     FStar_Syntax_Syntax.pos = uu____18327;
                     FStar_Syntax_Syntax.vars = uu____18328;_},uu____18329),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18330;
                     FStar_Syntax_Syntax.pos = uu____18331;
                     FStar_Syntax_Syntax.vars = uu____18332;_},uu____18333))
                   ->
                   let uu____18406 = destruct_flex_t t1  in
                   let uu____18407 = destruct_flex_t t2  in
                   flex_flex1 orig uu____18406 uu____18407
               | (FStar_Syntax_Syntax.Tm_uvar uu____18408,uu____18409) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18426 = destruct_flex_pattern env t1  in
                   solve_t_flex_rigid false orig uu____18426 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18433;
                     FStar_Syntax_Syntax.pos = uu____18434;
                     FStar_Syntax_Syntax.vars = uu____18435;_},uu____18436),uu____18437)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18474 = destruct_flex_pattern env t1  in
                   solve_t_flex_rigid false orig uu____18474 t2 wl
               | (uu____18481,FStar_Syntax_Syntax.Tm_uvar uu____18482) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____18499,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18500;
                     FStar_Syntax_Syntax.pos = uu____18501;
                     FStar_Syntax_Syntax.vars = uu____18502;_},uu____18503))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18540,FStar_Syntax_Syntax.Tm_type uu____18541) ->
                   solve_t' env
                     (let uu___152_18559 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___152_18559.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___152_18559.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___152_18559.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___152_18559.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___152_18559.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___152_18559.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___152_18559.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___152_18559.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___152_18559.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18560;
                     FStar_Syntax_Syntax.pos = uu____18561;
                     FStar_Syntax_Syntax.vars = uu____18562;_},uu____18563),FStar_Syntax_Syntax.Tm_type
                  uu____18564) ->
                   solve_t' env
                     (let uu___152_18602 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___152_18602.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___152_18602.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___152_18602.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___152_18602.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___152_18602.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___152_18602.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___152_18602.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___152_18602.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___152_18602.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18603,FStar_Syntax_Syntax.Tm_arrow uu____18604) ->
                   solve_t' env
                     (let uu___152_18634 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___152_18634.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___152_18634.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___152_18634.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___152_18634.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___152_18634.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___152_18634.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___152_18634.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___152_18634.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___152_18634.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18635;
                     FStar_Syntax_Syntax.pos = uu____18636;
                     FStar_Syntax_Syntax.vars = uu____18637;_},uu____18638),FStar_Syntax_Syntax.Tm_arrow
                  uu____18639) ->
                   solve_t' env
                     (let uu___152_18689 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___152_18689.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___152_18689.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___152_18689.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___152_18689.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___152_18689.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___152_18689.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___152_18689.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___152_18689.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___152_18689.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18690,uu____18691) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation
                         in
                      let uu____18710 =
                        let uu____18711 = is_top_level_prob orig  in
                        FStar_All.pipe_left Prims.op_Negation uu____18711  in
                      if uu____18710
                      then
                        let uu____18712 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___153_18718 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___153_18718.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___153_18718.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___153_18718.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___153_18718.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___153_18718.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___153_18718.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___153_18718.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___153_18718.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___153_18718.FStar_TypeChecker_Common.rank)
                             })
                           in
                        let uu____18719 = destruct_flex_pattern env t1  in
                        solve_t_flex_rigid false uu____18712 uu____18719 t2
                          wl
                      else
                        (let uu____18727 = base_and_refinement env t2  in
                         match uu____18727 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18756 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___154_18762 = problem  in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___154_18762.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___154_18762.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___154_18762.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___154_18762.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___154_18762.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___154_18762.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___154_18762.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___154_18762.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___154_18762.FStar_TypeChecker_Common.rank)
                                       })
                                     in
                                  let uu____18763 =
                                    destruct_flex_pattern env t1  in
                                  solve_t_flex_rigid false uu____18756
                                    uu____18763 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___155_18777 = y  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___155_18777.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___155_18777.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }  in
                                  let impl =
                                    guard_on_element wl problem y' phi  in
                                  let base_prob =
                                    let uu____18780 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_72  ->
                                         FStar_TypeChecker_Common.TProb _0_72)
                                      uu____18780
                                     in
                                  let guard =
                                    let uu____18792 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Util.mk_conj uu____18792
                                      impl
                                     in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl
                                     in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18800;
                     FStar_Syntax_Syntax.pos = uu____18801;
                     FStar_Syntax_Syntax.vars = uu____18802;_},uu____18803),uu____18804)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation
                         in
                      let uu____18843 =
                        let uu____18844 = is_top_level_prob orig  in
                        FStar_All.pipe_left Prims.op_Negation uu____18844  in
                      if uu____18843
                      then
                        let uu____18845 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___153_18851 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___153_18851.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___153_18851.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___153_18851.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___153_18851.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___153_18851.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___153_18851.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___153_18851.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___153_18851.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___153_18851.FStar_TypeChecker_Common.rank)
                             })
                           in
                        let uu____18852 = destruct_flex_pattern env t1  in
                        solve_t_flex_rigid false uu____18845 uu____18852 t2
                          wl
                      else
                        (let uu____18860 = base_and_refinement env t2  in
                         match uu____18860 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18889 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___154_18895 = problem  in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___154_18895.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___154_18895.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___154_18895.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___154_18895.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___154_18895.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___154_18895.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___154_18895.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___154_18895.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___154_18895.FStar_TypeChecker_Common.rank)
                                       })
                                     in
                                  let uu____18896 =
                                    destruct_flex_pattern env t1  in
                                  solve_t_flex_rigid false uu____18889
                                    uu____18896 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___155_18910 = y  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___155_18910.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___155_18910.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }  in
                                  let impl =
                                    guard_on_element wl problem y' phi  in
                                  let base_prob =
                                    let uu____18913 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_75  ->
                                         FStar_TypeChecker_Common.TProb _0_75)
                                      uu____18913
                                     in
                                  let guard =
                                    let uu____18925 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Util.mk_conj uu____18925
                                      impl
                                     in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl
                                     in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18933,FStar_Syntax_Syntax.Tm_uvar uu____18934) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18952 = base_and_refinement env t1  in
                      match uu____18952 with
                      | (t_base,uu____18964) ->
                          solve_t env
                            (let uu___156_18978 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___156_18978.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___156_18978.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___156_18978.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___156_18978.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___156_18978.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___156_18978.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___156_18978.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___156_18978.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18979,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18980;
                     FStar_Syntax_Syntax.pos = uu____18981;
                     FStar_Syntax_Syntax.vars = uu____18982;_},uu____18983))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____19021 = base_and_refinement env t1  in
                      match uu____19021 with
                      | (t_base,uu____19033) ->
                          solve_t env
                            (let uu___156_19047 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___156_19047.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___156_19047.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___156_19047.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___156_19047.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___156_19047.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___156_19047.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___156_19047.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___156_19047.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____19048,uu____19049) ->
                   let t21 =
                     let uu____19059 = base_and_refinement env t2  in
                     FStar_All.pipe_left force_refinement uu____19059  in
                   solve_t env
                     (let uu___157_19083 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___157_19083.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___157_19083.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___157_19083.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___157_19083.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___157_19083.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___157_19083.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___157_19083.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___157_19083.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___157_19083.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____19084,FStar_Syntax_Syntax.Tm_refine uu____19085) ->
                   let t11 =
                     let uu____19095 = base_and_refinement env t1  in
                     FStar_All.pipe_left force_refinement uu____19095  in
                   solve_t env
                     (let uu___158_19119 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___158_19119.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___158_19119.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___158_19119.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___158_19119.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___158_19119.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___158_19119.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___158_19119.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___158_19119.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___158_19119.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____19122,uu____19123) ->
                   let head1 =
                     let uu____19149 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19149
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19193 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19193
                       FStar_Pervasives_Native.fst
                      in
                   let uu____19234 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____19234
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____19249 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____19249
                      then
                        let guard =
                          let uu____19261 =
                            let uu____19262 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____19262 = FStar_Syntax_Util.Equal  in
                          if uu____19261
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19266 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____19266)
                           in
                        let uu____19269 = solve_prob orig guard [] wl  in
                        solve env uu____19269
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____19272,uu____19273) ->
                   let head1 =
                     let uu____19283 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19283
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19327 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19327
                       FStar_Pervasives_Native.fst
                      in
                   let uu____19368 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____19368
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____19383 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____19383
                      then
                        let guard =
                          let uu____19395 =
                            let uu____19396 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____19396 = FStar_Syntax_Util.Equal  in
                          if uu____19395
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19400 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____19400)
                           in
                        let uu____19403 = solve_prob orig guard [] wl  in
                        solve env uu____19403
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____19406,uu____19407) ->
                   let head1 =
                     let uu____19411 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19411
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19455 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19455
                       FStar_Pervasives_Native.fst
                      in
                   let uu____19496 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____19496
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____19511 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____19511
                      then
                        let guard =
                          let uu____19523 =
                            let uu____19524 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____19524 = FStar_Syntax_Util.Equal  in
                          if uu____19523
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19528 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____19528)
                           in
                        let uu____19531 = solve_prob orig guard [] wl  in
                        solve env uu____19531
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____19534,uu____19535) ->
                   let head1 =
                     let uu____19539 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19539
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19583 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19583
                       FStar_Pervasives_Native.fst
                      in
                   let uu____19624 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____19624
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____19639 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____19639
                      then
                        let guard =
                          let uu____19651 =
                            let uu____19652 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____19652 = FStar_Syntax_Util.Equal  in
                          if uu____19651
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19656 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____19656)
                           in
                        let uu____19659 = solve_prob orig guard [] wl  in
                        solve env uu____19659
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____19662,uu____19663) ->
                   let head1 =
                     let uu____19667 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19667
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19711 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19711
                       FStar_Pervasives_Native.fst
                      in
                   let uu____19752 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____19752
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____19767 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____19767
                      then
                        let guard =
                          let uu____19779 =
                            let uu____19780 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____19780 = FStar_Syntax_Util.Equal  in
                          if uu____19779
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19784 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19784)
                           in
                        let uu____19787 = solve_prob orig guard [] wl  in
                        solve env uu____19787
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19790,uu____19791) ->
                   let head1 =
                     let uu____19809 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19809
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19853 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19853
                       FStar_Pervasives_Native.fst
                      in
                   let uu____19894 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____19894
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____19909 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____19909
                      then
                        let guard =
                          let uu____19921 =
                            let uu____19922 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____19922 = FStar_Syntax_Util.Equal  in
                          if uu____19921
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19926 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19926)
                           in
                        let uu____19929 = solve_prob orig guard [] wl  in
                        solve env uu____19929
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19932,FStar_Syntax_Syntax.Tm_match uu____19933) ->
                   let head1 =
                     let uu____19959 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19959
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20003 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20003
                       FStar_Pervasives_Native.fst
                      in
                   let uu____20044 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____20044
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____20059 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____20059
                      then
                        let guard =
                          let uu____20071 =
                            let uu____20072 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____20072 = FStar_Syntax_Util.Equal  in
                          if uu____20071
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20076 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____20076)
                           in
                        let uu____20079 = solve_prob orig guard [] wl  in
                        solve env uu____20079
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20082,FStar_Syntax_Syntax.Tm_uinst uu____20083) ->
                   let head1 =
                     let uu____20093 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20093
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20137 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20137
                       FStar_Pervasives_Native.fst
                      in
                   let uu____20178 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____20178
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____20193 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____20193
                      then
                        let guard =
                          let uu____20205 =
                            let uu____20206 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____20206 = FStar_Syntax_Util.Equal  in
                          if uu____20205
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20210 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____20210)
                           in
                        let uu____20213 = solve_prob orig guard [] wl  in
                        solve env uu____20213
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20216,FStar_Syntax_Syntax.Tm_name uu____20217) ->
                   let head1 =
                     let uu____20221 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20221
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20265 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20265
                       FStar_Pervasives_Native.fst
                      in
                   let uu____20306 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____20306
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____20321 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____20321
                      then
                        let guard =
                          let uu____20333 =
                            let uu____20334 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____20334 = FStar_Syntax_Util.Equal  in
                          if uu____20333
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20338 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____20338)
                           in
                        let uu____20341 = solve_prob orig guard [] wl  in
                        solve env uu____20341
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20344,FStar_Syntax_Syntax.Tm_constant uu____20345) ->
                   let head1 =
                     let uu____20349 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20349
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20393 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20393
                       FStar_Pervasives_Native.fst
                      in
                   let uu____20434 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____20434
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____20449 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____20449
                      then
                        let guard =
                          let uu____20461 =
                            let uu____20462 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____20462 = FStar_Syntax_Util.Equal  in
                          if uu____20461
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20466 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____20466)
                           in
                        let uu____20469 = solve_prob orig guard [] wl  in
                        solve env uu____20469
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20472,FStar_Syntax_Syntax.Tm_fvar uu____20473) ->
                   let head1 =
                     let uu____20477 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20477
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20521 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20521
                       FStar_Pervasives_Native.fst
                      in
                   let uu____20562 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____20562
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____20577 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____20577
                      then
                        let guard =
                          let uu____20589 =
                            let uu____20590 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____20590 = FStar_Syntax_Util.Equal  in
                          if uu____20589
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20594 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____20594)
                           in
                        let uu____20597 = solve_prob orig guard [] wl  in
                        solve env uu____20597
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20600,FStar_Syntax_Syntax.Tm_app uu____20601) ->
                   let head1 =
                     let uu____20619 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20619
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20663 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20663
                       FStar_Pervasives_Native.fst
                      in
                   let uu____20704 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____20704
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____20719 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____20719
                      then
                        let guard =
                          let uu____20731 =
                            let uu____20732 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____20732 = FStar_Syntax_Util.Equal  in
                          if uu____20731
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20736 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____20736)
                           in
                        let uu____20739 = solve_prob orig guard [] wl  in
                        solve env uu____20739
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let uu____20742,uu____20743) ->
                   let uu____20756 =
                     let uu____20757 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____20758 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20757
                       uu____20758
                      in
                   failwith uu____20756
               | (FStar_Syntax_Syntax.Tm_delayed uu____20759,uu____20760) ->
                   let uu____20785 =
                     let uu____20786 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____20787 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20786
                       uu____20787
                      in
                   failwith uu____20785
               | (uu____20788,FStar_Syntax_Syntax.Tm_delayed uu____20789) ->
                   let uu____20814 =
                     let uu____20815 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____20816 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20815
                       uu____20816
                      in
                   failwith uu____20814
               | (uu____20817,FStar_Syntax_Syntax.Tm_let uu____20818) ->
                   let uu____20831 =
                     let uu____20832 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____20833 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____20832
                       uu____20833
                      in
                   failwith uu____20831
               | uu____20834 -> giveup env "head tag mismatch" orig)))

and (solve_c :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem ->
      worklist -> solution)
  =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let c1 = problem.FStar_TypeChecker_Common.lhs  in
        let c2 = problem.FStar_TypeChecker_Common.rhs  in
        let orig = FStar_TypeChecker_Common.CProb problem  in
        let sub_prob t1 rel t2 reason =
          mk_problem (p_scope orig) orig t1 rel t2
            FStar_Pervasives_Native.None reason
           in
        let solve_eq c1_comp c2_comp =
          (let uu____20870 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____20870
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____20872 =
               let uu____20873 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____20874 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20873 uu____20874
                in
             giveup env uu____20872 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____20894  ->
                    fun uu____20895  ->
                      match (uu____20894, uu____20895) with
                      | ((a1,uu____20913),(a2,uu____20915)) ->
                          let uu____20924 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg"
                             in
                          FStar_All.pipe_left
                            (fun _0_88  ->
                               FStar_TypeChecker_Common.TProb _0_88)
                            uu____20924)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args
                in
             let guard =
               let uu____20934 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs
                  in
               FStar_Syntax_Util.mk_conj_l uu____20934  in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl  in
             solve env (attempt sub_probs wl1))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____20958 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20965)::[] -> wp1
              | uu____20982 ->
                  let uu____20991 =
                    let uu____20992 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name)
                       in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20992
                     in
                  failwith uu____20991
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____21000 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____21000]
              | x -> x  in
            let uu____21002 =
              let uu____21011 =
                let uu____21012 =
                  let uu____21013 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____21013 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____21012  in
              [uu____21011]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____21002;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____21014 = lift_c1 ()  in solve_eq uu____21014 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___112_21020  ->
                       match uu___112_21020 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____21021 -> false))
                in
             let uu____21022 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____21056)::uu____21057,(wp2,uu____21059)::uu____21060)
                   -> (wp1, wp2)
               | uu____21117 ->
                   let uu____21138 =
                     let uu____21143 =
                       let uu____21144 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____21145 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____21144 uu____21145
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____21143)
                      in
                   FStar_Errors.raise_error uu____21138
                     env.FStar_TypeChecker_Env.range
                in
             match uu____21022 with
             | (wpc1,wpc2) ->
                 let uu____21164 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____21164
                 then
                   let uu____21167 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____21167 wl
                 else
                   (let uu____21171 =
                      let uu____21178 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____21178  in
                    match uu____21171 with
                    | (c2_decl,qualifiers) ->
                        let uu____21199 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____21199
                        then
                          let c1_repr =
                            let uu____21203 =
                              let uu____21204 =
                                let uu____21205 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____21205  in
                              let uu____21206 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21204 uu____21206
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21203
                             in
                          let c2_repr =
                            let uu____21208 =
                              let uu____21209 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____21210 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21209 uu____21210
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21208
                             in
                          let prob =
                            let uu____21212 =
                              let uu____21217 =
                                let uu____21218 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____21219 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____21218
                                  uu____21219
                                 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____21217
                               in
                            FStar_TypeChecker_Common.TProb uu____21212  in
                          let wl1 =
                            let uu____21221 =
                              let uu____21224 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_Pervasives_Native.Some uu____21224  in
                            solve_prob orig uu____21221 [] wl  in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____21233 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21233
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____21236 =
                                     let uu____21239 =
                                       let uu____21240 =
                                         let uu____21255 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____21256 =
                                           let uu____21259 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____21260 =
                                             let uu____21263 =
                                               let uu____21264 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____21264
                                                in
                                             [uu____21263]  in
                                           uu____21259 :: uu____21260  in
                                         (uu____21255, uu____21256)  in
                                       FStar_Syntax_Syntax.Tm_app uu____21240
                                        in
                                     FStar_Syntax_Syntax.mk uu____21239  in
                                   uu____21236 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____21273 =
                                    let uu____21276 =
                                      let uu____21277 =
                                        let uu____21292 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____21293 =
                                          let uu____21296 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____21297 =
                                            let uu____21300 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____21301 =
                                              let uu____21304 =
                                                let uu____21305 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____21305
                                                 in
                                              [uu____21304]  in
                                            uu____21300 :: uu____21301  in
                                          uu____21296 :: uu____21297  in
                                        (uu____21292, uu____21293)  in
                                      FStar_Syntax_Syntax.Tm_app uu____21277
                                       in
                                    FStar_Syntax_Syntax.mk uu____21276  in
                                  uu____21273 FStar_Pervasives_Native.None r)
                              in
                           let base_prob =
                             let uu____21312 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type"
                                in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____21312
                              in
                           let wl1 =
                             let uu____21322 =
                               let uu____21325 =
                                 let uu____21328 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____21328 g  in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____21325
                                in
                             solve_prob orig uu____21322 [] wl  in
                           solve env (attempt [base_prob] wl1))))
           in
        let uu____21341 = FStar_Util.physical_equality c1 c2  in
        if uu____21341
        then
          let uu____21342 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____21342
        else
          ((let uu____21345 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____21345
            then
              let uu____21346 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____21347 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____21346
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____21347
            else ());
           (let uu____21349 =
              let uu____21354 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____21355 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____21354, uu____21355)  in
            match uu____21349 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21359),FStar_Syntax_Syntax.Total
                    (t2,uu____21361)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21378 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21378 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21381,FStar_Syntax_Syntax.Total uu____21382) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21400),FStar_Syntax_Syntax.Total
                    (t2,uu____21402)) ->
                     let uu____21419 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21419 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21423),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21425)) ->
                     let uu____21442 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21442 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21446),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21448)) ->
                     let uu____21465 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21465 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21468,FStar_Syntax_Syntax.Comp uu____21469) ->
                     let uu____21478 =
                       let uu___159_21483 = problem  in
                       let uu____21488 =
                         let uu____21489 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21489
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___159_21483.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21488;
                         FStar_TypeChecker_Common.relation =
                           (uu___159_21483.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___159_21483.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___159_21483.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___159_21483.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___159_21483.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___159_21483.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___159_21483.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___159_21483.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21478 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21490,FStar_Syntax_Syntax.Comp uu____21491) ->
                     let uu____21500 =
                       let uu___159_21505 = problem  in
                       let uu____21510 =
                         let uu____21511 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21511
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___159_21505.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21510;
                         FStar_TypeChecker_Common.relation =
                           (uu___159_21505.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___159_21505.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___159_21505.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___159_21505.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___159_21505.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___159_21505.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___159_21505.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___159_21505.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21500 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21512,FStar_Syntax_Syntax.GTotal uu____21513) ->
                     let uu____21522 =
                       let uu___160_21527 = problem  in
                       let uu____21532 =
                         let uu____21533 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21533
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___160_21527.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___160_21527.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___160_21527.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21532;
                         FStar_TypeChecker_Common.element =
                           (uu___160_21527.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___160_21527.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___160_21527.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___160_21527.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___160_21527.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___160_21527.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21522 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21534,FStar_Syntax_Syntax.Total uu____21535) ->
                     let uu____21544 =
                       let uu___160_21549 = problem  in
                       let uu____21554 =
                         let uu____21555 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21555
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___160_21549.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___160_21549.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___160_21549.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21554;
                         FStar_TypeChecker_Common.element =
                           (uu___160_21549.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___160_21549.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___160_21549.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___160_21549.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___160_21549.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___160_21549.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21544 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21556,FStar_Syntax_Syntax.Comp uu____21557) ->
                     let uu____21558 =
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
                               FStar_TypeChecker_Common.SUB))
                        in
                     if uu____21558
                     then
                       let uu____21559 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____21559 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21565 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21575 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____21576 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____21575, uu____21576))
                             in
                          match uu____21565 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11
                              in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21
                              in
                           (let uu____21583 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____21583
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21585 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____21585 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21588 =
                                  let uu____21589 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____21590 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____21589 uu____21590
                                   in
                                giveup env uu____21588 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____21595 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21633  ->
              match uu____21633 with
              | (uu____21646,uu____21647,u,uu____21649,uu____21650,uu____21651)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____21595 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____21682 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____21682 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____21700 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21728  ->
                match uu____21728 with
                | (u1,u2) ->
                    let uu____21735 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____21736 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____21735 uu____21736))
         in
      FStar_All.pipe_right uu____21700 (FStar_String.concat ", ")  in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1
  
let (guard_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun env  ->
    fun g  ->
      match ((g.FStar_TypeChecker_Env.guard_f),
              (g.FStar_TypeChecker_Env.deferred),
              (g.FStar_TypeChecker_Env.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21753,[])) -> "{}"
      | uu____21778 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21795 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____21795
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____21798 =
              FStar_List.map
                (fun uu____21808  ->
                   match uu____21808 with
                   | (uu____21813,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____21798 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____21818 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21818 imps
  
let new_t_problem :
  'Auu____21826 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21826 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21826)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21860 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel")
                   in
                if uu____21860
                then
                  let uu____21861 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs  in
                  let uu____21862 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs  in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21861
                    (rel_to_string rel) uu____21862
                else "TOP"  in
              let p = new_problem env lhs rel rhs elt loc reason  in p
  
let (new_t_prob :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Common.rel ->
        FStar_Syntax_Syntax.term ->
          (FStar_TypeChecker_Common.prob,FStar_Syntax_Syntax.bv)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun t1  ->
      fun rel  ->
        fun t2  ->
          let x =
            let uu____21886 =
              let uu____21889 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____21889
               in
            FStar_Syntax_Syntax.new_bv uu____21886 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____21898 =
              let uu____21901 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____21901
               in
            let uu____21904 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____21898 uu____21904  in
          ((FStar_TypeChecker_Common.TProb p), x)
  
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob,Prims.string)
         FStar_Pervasives_Native.tuple2 ->
         FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option)
        -> FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun probs  ->
      fun err  ->
        let probs1 =
          let uu____21934 = FStar_Options.eager_inference ()  in
          if uu____21934
          then
            let uu___161_21935 = probs  in
            {
              attempting = (uu___161_21935.attempting);
              wl_deferred = (uu___161_21935.wl_deferred);
              ctr = (uu___161_21935.ctr);
              defer_ok = false;
              smt_ok = (uu___161_21935.smt_ok);
              tcenv = (uu___161_21935.tcenv)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            ((let uu____21946 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____21946
              then
                let uu____21947 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____21947
              else ());
             (let result = err (d, s)  in
              FStar_Syntax_Unionfind.rollback tx; result))
  
let (simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____21961 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____21961
            then
              let uu____21962 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21962
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____21966 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____21966
             then
               let uu____21967 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21967
             else ());
            (let f2 =
               let uu____21970 =
                 let uu____21971 = FStar_Syntax_Util.unmeta f1  in
                 uu____21971.FStar_Syntax_Syntax.n  in
               match uu____21970 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21975 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___162_21976 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___162_21976.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___162_21976.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___162_21976.FStar_TypeChecker_Env.implicits)
             })))
  
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some d ->
            let uu____21995 =
              let uu____21996 =
                let uu____21997 =
                  let uu____21998 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____21998
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21997;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____21996  in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____21995
  
let with_guard_no_simp :
  'Auu____22025 .
    'Auu____22025 ->
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
            let uu____22045 =
              let uu____22046 =
                let uu____22047 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____22047
                  (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____22046;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____22045
  
let (try_teq :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____22085 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____22085
           then
             let uu____22086 = FStar_Syntax_Print.term_to_string t1  in
             let uu____22087 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____22086
               uu____22087
           else ());
          (let prob =
             let uu____22090 =
               let uu____22095 = FStar_TypeChecker_Env.get_range env  in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____22095
                in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____22090
              in
           let g =
             let uu____22103 =
               let uu____22106 = singleton' env prob smt_ok  in
               solve_and_commit env uu____22106
                 (fun uu____22108  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob) uu____22103  in
           g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22126 = try_teq true env t1 t2  in
        match uu____22126 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____22130 = FStar_TypeChecker_Env.get_range env  in
              let uu____22131 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____22130 uu____22131);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____22138 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____22138
              then
                let uu____22139 = FStar_Syntax_Print.term_to_string t1  in
                let uu____22140 = FStar_Syntax_Print.term_to_string t2  in
                let uu____22141 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____22139
                  uu____22140 uu____22141
              else ());
             g)
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____22155 = FStar_TypeChecker_Env.get_range env  in
          let uu____22156 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____22155 uu____22156
  
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____22173 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22173
         then
           let uu____22174 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____22175 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____22174
             uu____22175
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB  in
         let prob =
           let uu____22180 =
             let uu____22185 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____22185 "sub_comp"
              in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____22180
            in
         let uu____22190 =
           let uu____22193 = singleton env prob  in
           solve_and_commit env uu____22193
             (fun uu____22195  -> FStar_Pervasives_Native.None)
            in
         FStar_All.pipe_left (with_guard env prob) uu____22190)
  
let (solve_universe_inequalities' :
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                                 FStar_Syntax_Syntax.universe)
                                                 FStar_Pervasives_Native.tuple2
                                                 Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.unit)
  =
  fun tx  ->
    fun env  ->
      fun uu____22224  ->
        match uu____22224 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22263 =
                 let uu____22268 =
                   let uu____22269 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____22270 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____22269 uu____22270
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____22268)  in
               let uu____22271 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____22263 uu____22271)
               in
            let equiv1 v1 v' =
              let uu____22279 =
                let uu____22284 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____22285 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____22284, uu____22285)  in
              match uu____22279 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22304 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22334 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____22334 with
                      | FStar_Syntax_Syntax.U_unif uu____22341 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22370  ->
                                    match uu____22370 with
                                    | (u,v') ->
                                        let uu____22379 = equiv1 v1 v'  in
                                        if uu____22379
                                        then
                                          let uu____22382 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____22382 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____22398 -> []))
               in
            let uu____22403 =
              let wl =
                let uu___163_22407 = empty_worklist env  in
                {
                  attempting = (uu___163_22407.attempting);
                  wl_deferred = (uu___163_22407.wl_deferred);
                  ctr = (uu___163_22407.ctr);
                  defer_ok = false;
                  smt_ok = (uu___163_22407.smt_ok);
                  tcenv = (uu___163_22407.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22425  ->
                      match uu____22425 with
                      | (lb,v1) ->
                          let uu____22432 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____22432 with
                           | USolved wl1 -> ()
                           | uu____22434 -> fail lb v1)))
               in
            let rec check_ineq uu____22442 =
              match uu____22442 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22451) -> true
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
                      uu____22474,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22476,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22487) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22494,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22502 -> false)
               in
            let uu____22507 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22522  ->
                      match uu____22522 with
                      | (u,v1) ->
                          let uu____22529 = check_ineq (u, v1)  in
                          if uu____22529
                          then true
                          else
                            ((let uu____22532 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____22532
                              then
                                let uu____22533 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____22534 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____22533
                                  uu____22534
                              else ());
                             false)))
               in
            if uu____22507
            then ()
            else
              ((let uu____22538 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____22538
                then
                  ((let uu____22540 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22540);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22550 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22550))
                else ());
               (let uu____22560 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____22560))
  
let (solve_universe_inequalities :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                               FStar_Syntax_Syntax.universe)
                                               FStar_Pervasives_Native.tuple2
                                               Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.unit)
  =
  fun env  ->
    fun ineqs  ->
      let tx = FStar_Syntax_Unionfind.new_transaction ()  in
      solve_universe_inequalities' tx env ineqs;
      FStar_Syntax_Unionfind.commit tx
  
let rec (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let fail uu____22608 =
        match uu____22608 with
        | (d,s) ->
            let msg = explain env d s  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
              (p_loc d)
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____22622 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____22622
       then
         let uu____22623 = wl_to_string wl  in
         let uu____22624 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits)
            in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22623 uu____22624
       else ());
      (let g1 =
         let uu____22639 = solve_and_commit env wl fail  in
         match uu____22639 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___164_22652 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___164_22652.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___164_22652.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___164_22652.FStar_TypeChecker_Env.implicits)
             }
         | uu____22657 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___165_22661 = g1  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___165_22661.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___165_22661.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___165_22661.FStar_TypeChecker_Env.implicits)
        }))
  
let (last_proof_ns :
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (maybe_update_proof_ns : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns  in
    let uu____22713 = FStar_ST.op_Bang last_proof_ns  in
    match uu____22713 with
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
  
let (discharge_guard' :
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t ->
        Prims.bool ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
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
                 (FStar_Options.Other "Tac"))
             in
          let g1 = solve_deferred_constraints env g  in
          let ret_g =
            let uu___166_22816 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___166_22816.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___166_22816.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___166_22816.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____22817 =
            let uu____22818 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____22818  in
          if uu____22817
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22826 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____22827 =
                       let uu____22828 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22828
                        in
                     FStar_Errors.diag uu____22826 uu____22827)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____22832 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____22833 =
                        let uu____22834 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22834
                         in
                      FStar_Errors.diag uu____22832 uu____22833)
                   else ();
                   (let uu____22836 = check_trivial vc1  in
                    match uu____22836 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22843 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22844 =
                                let uu____22845 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22845
                                 in
                              FStar_Errors.diag uu____22843 uu____22844)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22850 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22851 =
                                let uu____22852 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22852
                                 in
                              FStar_Errors.diag uu____22850 uu____22851)
                           else ();
                           (let vcs =
                              let uu____22863 = FStar_Options.use_tactics ()
                                 in
                              if uu____22863
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22882  ->
                                     (let uu____22884 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left
                                        FStar_Pervasives.ignore uu____22884);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____22886 =
                                   let uu____22893 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____22893)  in
                                 [uu____22886])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22927  ->
                                    match uu____22927 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal
                                           in
                                        let uu____22938 = check_trivial goal1
                                           in
                                        (match uu____22938 with
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
                                                (let uu____22946 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22947 =
                                                   let uu____22948 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   let uu____22949 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22948 uu____22949
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22946 uu____22947)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22952 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22953 =
                                                   let uu____22954 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22954
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22952 uu____22953)
                                              else ();
                                              (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                use_env_range_msg env1 goal2;
                                              FStar_Options.pop ())))));
                           FStar_Pervasives_Native.Some ret_g)))))
  
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____22964 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____22964 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22970 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____22970
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____22977 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____22977 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let (resolve_implicits' :
  Prims.bool ->
    Prims.bool ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun must_total  ->
    fun forcelax  ->
      fun g  ->
        let unresolved u =
          let uu____22996 = FStar_Syntax_Unionfind.find u  in
          match uu____22996 with
          | FStar_Pervasives_Native.None  -> true
          | uu____22999 -> false  in
        let rec until_fixpoint acc implicits =
          let uu____23017 = acc  in
          match uu____23017 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____23103 = hd1  in
                   (match uu____23103 with
                    | (uu____23116,env,u,tm,k,r) ->
                        let uu____23122 = unresolved u  in
                        if uu____23122
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env tm
                              in
                           let env1 =
                             if forcelax
                             then
                               let uu___167_23152 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___167_23152.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___167_23152.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___167_23152.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___167_23152.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___167_23152.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___167_23152.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___167_23152.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___167_23152.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___167_23152.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___167_23152.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___167_23152.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___167_23152.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___167_23152.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___167_23152.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___167_23152.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___167_23152.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___167_23152.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___167_23152.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___167_23152.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___167_23152.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___167_23152.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___167_23152.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___167_23152.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___167_23152.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___167_23152.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___167_23152.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___167_23152.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___167_23152.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___167_23152.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___167_23152.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___167_23152.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___167_23152.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___167_23152.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___167_23152.FStar_TypeChecker_Env.dep_graph)
                               }
                             else env  in
                           (let uu____23155 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck")
                               in
                            if uu____23155
                            then
                              let uu____23156 =
                                FStar_Syntax_Print.uvar_to_string u  in
                              let uu____23157 =
                                FStar_Syntax_Print.term_to_string tm1  in
                              let uu____23158 =
                                FStar_Syntax_Print.term_to_string k  in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____23156 uu____23157 uu____23158
                            else ());
                           (let g1 =
                              try
                                env1.FStar_TypeChecker_Env.check_type_of
                                  must_total env1 tm1 k
                              with
                              | e ->
                                  ((let uu____23169 =
                                      let uu____23178 =
                                        let uu____23185 =
                                          let uu____23186 =
                                            FStar_Syntax_Print.uvar_to_string
                                              u
                                             in
                                          let uu____23187 =
                                            FStar_TypeChecker_Normalize.term_to_string
                                              env1 tm1
                                             in
                                          FStar_Util.format2
                                            "Failed while checking implicit %s set to %s"
                                            uu____23186 uu____23187
                                           in
                                        (FStar_Errors.Error_BadImplicit,
                                          uu____23185, r)
                                         in
                                      [uu____23178]  in
                                    FStar_Errors.add_errors uu____23169);
                                   FStar_Exn.raise e)
                               in
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___170_23201 = g1  in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___170_23201.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___170_23201.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___170_23201.FStar_TypeChecker_Env.implicits)
                                }
                              else g1  in
                            let g' =
                              let uu____23204 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____23210  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true
                                 in
                              match uu____23204 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                               in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1))))
           in
        let uu___171_23238 = g  in
        let uu____23239 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___171_23238.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___171_23238.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___171_23238.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____23239
        }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t) =
  fun g  -> resolve_implicits' true false g 
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t) =
  fun g  -> resolve_implicits' false true g 
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit) =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____23293 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____23293 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23306 = discharge_guard env g1  in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____23306
      | (reason,uu____23308,uu____23309,e,t,r)::uu____23313 ->
          let uu____23340 =
            let uu____23345 =
              let uu____23346 = FStar_Syntax_Print.term_to_string t  in
              let uu____23347 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format2
                "Failed to resolve implicit argument of type '%s' introduced in %s"
                uu____23346 uu____23347
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____23345)
             in
          FStar_Errors.raise_error uu____23340 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___172_23354 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___172_23354.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___172_23354.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___172_23354.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____23377 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23377 with
      | FStar_Pervasives_Native.Some uu____23382 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23392 = try_teq false env t1 t2  in
        match uu____23392 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> discharge_guard_nosmt env g
  
let (check_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23412 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23412
         then
           let uu____23413 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23414 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23413
             uu____23414
         else ());
        (let uu____23416 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____23416 with
         | (prob,x) ->
             let g =
               let uu____23432 =
                 let uu____23435 = singleton' env prob true  in
                 solve_and_commit env uu____23435
                   (fun uu____23437  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23432  in
             ((let uu____23447 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____23447
               then
                 let uu____23448 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____23449 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____23450 =
                   let uu____23451 = FStar_Util.must g  in
                   guard_to_string env uu____23451  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23448 uu____23449 uu____23450
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   FStar_Pervasives_Native.Some (x, g1))))
  
let (get_subtyping_predicate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23479 = check_subtyping env t1 t2  in
        match uu____23479 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23498 =
              let uu____23499 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____23499 g  in
            FStar_Pervasives_Native.Some uu____23498
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23511 = check_subtyping env t1 t2  in
        match uu____23511 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23530 =
              let uu____23531 =
                let uu____23532 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____23532]  in
              close_guard env uu____23531 g  in
            FStar_Pervasives_Native.Some uu____23530
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23543 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23543
         then
           let uu____23544 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23545 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23544
             uu____23545
         else ());
        (let uu____23547 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____23547 with
         | (prob,x) ->
             let g =
               let uu____23557 =
                 let uu____23560 = singleton' env prob false  in
                 solve_and_commit env uu____23560
                   (fun uu____23562  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23557  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23573 =
                      let uu____23574 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____23574]  in
                    close_guard env uu____23573 g1  in
                  discharge_guard_nosmt env g2))
  