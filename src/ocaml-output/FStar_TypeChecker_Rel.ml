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
          let uu___112_91 = g  in
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
  
let (abstract_guard :
  FStar_Syntax_Syntax.binder ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun b  -> fun g  -> abstract_guard_n [b] g 
let (def_check_closed_in :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____110 = FStar_Options.defensive ()  in
          if uu____110
          then
            let s = FStar_TypeChecker_Env.unbound_vars e t  in
            let uu____114 =
              let uu____115 = FStar_Util.set_is_empty s  in
              Prims.op_Negation uu____115  in
            (if uu____114
             then
               let uu____116 =
                 let uu____121 =
                   let uu____122 = FStar_Syntax_Print.term_to_string t  in
                   let uu____123 =
                     let uu____124 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____124
                       (FStar_Syntax_Print.bvs_to_string ", ")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____122 uu____123
                    in
                 (FStar_Errors.Warning_Defensive, uu____121)  in
               FStar_Errors.log_issue rng uu____116
             else ())
          else ()
  
let (def_check_closed :
  FStar_Range.range -> Prims.string -> FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun rng  ->
    fun msg  ->
      fun t  ->
        let uu____140 = FStar_Options.defensive ()  in
        if uu____140
        then
          let s = FStar_Syntax_Free.names t  in
          let uu____144 =
            let uu____145 = FStar_Util.set_is_empty s  in
            Prims.op_Negation uu____145  in
          (if uu____144
           then
             let uu____146 =
               let uu____151 =
                 let uu____152 = FStar_Syntax_Print.term_to_string t  in
                 let uu____153 =
                   let uu____154 = FStar_Util.set_elements s  in
                   FStar_All.pipe_right uu____154
                     (FStar_Syntax_Print.bvs_to_string ", ")
                    in
                 FStar_Util.format3
                   "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                   msg uu____152 uu____153
                  in
               (FStar_Errors.Warning_Defensive, uu____151)  in
             FStar_Errors.log_issue rng uu____146
           else ())
        else ()
  
let (apply_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t)
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___113_168 = g  in
          let uu____169 =
            let uu____170 =
              let uu____171 =
                let uu____174 =
                  let uu____175 =
                    let uu____190 =
                      let uu____193 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____193]  in
                    (f, uu____190)  in
                  FStar_Syntax_Syntax.Tm_app uu____175  in
                FStar_Syntax_Syntax.mk uu____174  in
              uu____171 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_40  -> FStar_TypeChecker_Common.NonTrivial _0_40)
              uu____170
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____169;
            FStar_TypeChecker_Env.deferred =
              (uu___113_168.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___113_168.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___113_168.FStar_TypeChecker_Env.implicits)
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
          let uu___114_211 = g  in
          let uu____212 =
            let uu____213 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____213  in
          {
            FStar_TypeChecker_Env.guard_f = uu____212;
            FStar_TypeChecker_Env.deferred =
              (uu___114_211.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___114_211.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___114_211.FStar_TypeChecker_Env.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> Prims.unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____217 -> failwith "impossible"
  
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
          let uu____228 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____228
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____232 =
      let uu____233 = FStar_Syntax_Util.unmeta t  in
      uu____233.FStar_Syntax_Syntax.n  in
    match uu____232 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____237 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____268 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____268;
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
                       let uu____335 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____335
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___115_337 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___115_337.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___115_337.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___115_337.FStar_TypeChecker_Env.implicits)
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
               let uu____356 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____356
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
            let uu___116_369 = g  in
            let uu____370 =
              let uu____371 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____371  in
            {
              FStar_TypeChecker_Env.guard_f = uu____370;
              FStar_TypeChecker_Env.deferred =
                (uu___116_369.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___116_369.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___116_369.FStar_TypeChecker_Env.implicits)
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
        | uu____401 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder)
               in
            let k' =
              let uu____426 = FStar_Syntax_Syntax.mk_Total k  in
              FStar_Syntax_Util.arrow binders uu____426  in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                FStar_Pervasives_Native.None r
               in
            let uu____434 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                FStar_Pervasives_Native.None r
               in
            (uu____434, uv1)
  
let (mk_eq2 :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____462 = FStar_Syntax_Util.type_u ()  in
        match uu____462 with
        | (t_type,u) ->
            let uu____469 =
              let uu____474 = FStar_TypeChecker_Env.all_binders env  in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____474 t_type  in
            (match uu____469 with
             | (tt,uu____476) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
  
type uvi =
  | TERM of
  ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____509 -> false
  
let (__proj__TERM__item___0 :
  uvi ->
    ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
       FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____549 -> false
  
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
    match projectee with | Success _0 -> true | uu____735 -> false
  
let (__proj__Success__item___0 :
  solution -> FStar_TypeChecker_Common.deferred) =
  fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____751 -> false
  
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
    match projectee with | COVARIANT  -> true | uu____774 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____778 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____782 -> false
  
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem[@@deriving show]
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
[@@deriving show]
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem[@@deriving
                                                                   show]
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___84_805  ->
    match uu___84_805 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let compact = FStar_Syntax_Print.term_to_string t  in
    let detail =
      let uu____811 =
        let uu____812 = FStar_Syntax_Subst.compress t  in
        uu____812.FStar_Syntax_Syntax.n  in
      match uu____811 with
      | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
          let uu____841 = FStar_Syntax_Print.uvar_to_string u  in
          let uu____842 = FStar_Syntax_Print.term_to_string t1  in
          FStar_Util.format2 "%s : %s" uu____841 uu____842
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
             FStar_Syntax_Syntax.pos = uu____845;
             FStar_Syntax_Syntax.vars = uu____846;_},args)
          ->
          let uu____892 = FStar_Syntax_Print.uvar_to_string u  in
          let uu____893 = FStar_Syntax_Print.term_to_string ty  in
          let uu____894 = FStar_Syntax_Print.args_to_string args  in
          FStar_Util.format3 "(%s : %s) %s" uu____892 uu____893 uu____894
      | uu____895 -> "--"  in
    let uu____896 = FStar_Syntax_Print.tag_of_term t  in
    FStar_Util.format3 "%s (%s)\t%s" compact uu____896 detail
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___85_902  ->
      match uu___85_902 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____908 =
            let uu____911 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____912 =
              let uu____915 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____916 =
                let uu____919 =
                  let uu____922 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____922]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____919
                 in
              uu____915 :: uu____916  in
            uu____911 :: uu____912  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s" uu____908
      | FStar_TypeChecker_Common.CProb p ->
          let uu____928 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____929 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____930 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____928 uu____929
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____930
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___86_936  ->
      match uu___86_936 with
      | UNIV (u,t) ->
          let x =
            let uu____940 = FStar_Options.hide_uvar_nums ()  in
            if uu____940
            then "?"
            else
              (let uu____942 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____942 FStar_Util.string_of_int)
             in
          let uu____943 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____943
      | TERM ((u,uu____945),t) ->
          let x =
            let uu____952 = FStar_Options.hide_uvar_nums ()  in
            if uu____952
            then "?"
            else
              (let uu____954 = FStar_Syntax_Unionfind.uvar_id u  in
               FStar_All.pipe_right uu____954 FStar_Util.string_of_int)
             in
          let uu____955 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____955
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____966 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____966 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____978 =
      let uu____981 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____981
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____978 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____992 .
    (FStar_Syntax_Syntax.term,'Auu____992) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1009 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1027  ->
              match uu____1027 with
              | (x,uu____1033) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1009 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    let uu____1039 =
      let uu____1040 = FStar_Options.eager_inference ()  in
      Prims.op_Negation uu____1040  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1039;
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
        let uu___117_1056 = empty_worklist env  in
        {
          attempting = [prob];
          wl_deferred = (uu___117_1056.wl_deferred);
          ctr = (uu___117_1056.ctr);
          defer_ok = (uu___117_1056.defer_ok);
          smt_ok;
          tcenv = (uu___117_1056.tcenv)
        }
  
let (singleton :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist) =
  fun env  -> fun prob  -> singleton' env prob true 
let wl_of_guard :
  'Auu____1066 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1066,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___118_1087 = empty_worklist env  in
      let uu____1088 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1088;
        wl_deferred = (uu___118_1087.wl_deferred);
        ctr = (uu___118_1087.ctr);
        defer_ok = false;
        smt_ok = (uu___118_1087.smt_ok);
        tcenv = (uu___118_1087.tcenv)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___119_1102 = wl  in
        {
          attempting = (uu___119_1102.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___119_1102.ctr);
          defer_ok = (uu___119_1102.defer_ok);
          smt_ok = (uu___119_1102.smt_ok);
          tcenv = (uu___119_1102.tcenv)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      let uu___120_1119 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___120_1119.wl_deferred);
        ctr = (uu___120_1119.ctr);
        defer_ok = (uu___120_1119.defer_ok);
        smt_ok = (uu___120_1119.smt_ok);
        tcenv = (uu___120_1119.tcenv)
      }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1130 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1130
         then
           let uu____1131 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1131
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___87_1135  ->
    match uu___87_1135 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1139 'Auu____1140 .
    ('Auu____1140,'Auu____1139) FStar_TypeChecker_Common.problem ->
      ('Auu____1140,'Auu____1139) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___121_1157 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___121_1157.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___121_1157.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___121_1157.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___121_1157.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___121_1157.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___121_1157.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___121_1157.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1165 'Auu____1166 .
    ('Auu____1166,'Auu____1165) FStar_TypeChecker_Common.problem ->
      ('Auu____1166,'Auu____1165) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___88_1186  ->
    match uu___88_1186 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.CProb _0_42)
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___89_1210  ->
      match uu___89_1210 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___90_1213  ->
    match uu___90_1213 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___91_1226  ->
    match uu___91_1226 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___92_1241  ->
    match uu___92_1241 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___93_1256  ->
    match uu___93_1256 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_guard :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___94_1273  ->
    match uu___94_1273 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_scope : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders)
  =
  fun prob  ->
    let r =
      match prob with
      | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
      | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
       in
    match r with
    | [] -> r
    | (bv,uu____1307)::uu____1308 ->
        (def_check_closed (p_loc prob) "p_scope" bv.FStar_Syntax_Syntax.sort;
         r)
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___95_1322  ->
    match uu___95_1322 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1344 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1344 = (Prims.parse_int "1")
  
let (next_pid : Prims.unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1356  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____1441 'Auu____1442 .
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob ->
        'Auu____1442 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1442 ->
              'Auu____1441 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1442,'Auu____1441)
                    FStar_TypeChecker_Common.problem
  =
  fun scope  ->
    fun orig  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun reason  ->
                let uu____1479 = next_pid ()  in
                let uu____1480 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0
                   in
                {
                  FStar_TypeChecker_Common.pid = uu____1479;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1480;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
  
let new_problem :
  'Auu____1494 'Auu____1495 .
    FStar_TypeChecker_Env.env ->
      'Auu____1495 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1495 ->
            'Auu____1494 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1495,'Auu____1494)
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
                let uu____1533 = next_pid ()  in
                let uu____1534 =
                  new_uvar FStar_Range.dummyRange scope
                    FStar_Syntax_Util.ktype0
                   in
                {
                  FStar_TypeChecker_Common.pid = uu____1533;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = uu____1534;
                  FStar_TypeChecker_Common.scope = scope;
                  FStar_TypeChecker_Common.reason = [reason];
                  FStar_TypeChecker_Common.loc = loc;
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }
  
let problem_using_guard :
  'Auu____1547 'Auu____1548 .
    FStar_TypeChecker_Common.prob ->
      'Auu____1548 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1548 ->
            'Auu____1547 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____1548,'Auu____1547) FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____1581 = next_pid ()  in
              let uu____1582 = p_scope orig  in
              {
                FStar_TypeChecker_Common.pid = uu____1581;
                FStar_TypeChecker_Common.lhs = lhs;
                FStar_TypeChecker_Common.relation = rel;
                FStar_TypeChecker_Common.rhs = rhs;
                FStar_TypeChecker_Common.element = elt;
                FStar_TypeChecker_Common.logical_guard = (p_guard orig);
                FStar_TypeChecker_Common.scope = uu____1582;
                FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
                FStar_TypeChecker_Common.loc = (p_loc orig);
                FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
              }
  
let guard_on_element :
  'Auu____1588 .
    worklist ->
      ('Auu____1588,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
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
        let uu____1638 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel")
           in
        if uu____1638
        then
          let uu____1639 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____1640 = prob_to_string env d  in
          let uu____1641 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1639 uu____1640 uu____1641 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1647 -> failwith "impossible"  in
           let uu____1648 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1662 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____1663 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____1662, uu____1663)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1669 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____1670 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____1669, uu____1670)
              in
           match uu____1648 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> Prims.unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___96_1686  ->
            match uu___96_1686 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1698 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1700),t) ->
                (def_check_closed t.FStar_Syntax_Syntax.pos "commit" t;
                 FStar_Syntax_Util.set_uvar u t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___97_1721  ->
           match uu___97_1721 with
           | UNIV uu____1724 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1730),t) ->
               let uu____1736 = FStar_Syntax_Unionfind.equiv uv u  in
               if uu____1736
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
        (fun uu___98_1756  ->
           match uu___98_1756 with
           | UNIV (u',t) ->
               let uu____1761 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____1761
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1765 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____1772 =
        let uu____1773 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____1773
         in
      FStar_Syntax_Subst.compress uu____1772
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____1780 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____1780
  
let norm_arg :
  'Auu____1784 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____1784) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____1784)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____1805 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____1805, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____1836  ->
              match uu____1836 with
              | (x,imp) ->
                  let uu____1847 =
                    let uu___122_1848 = x  in
                    let uu____1849 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___122_1848.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___122_1848.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1849
                    }  in
                  (uu____1847, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1864 = aux u3  in FStar_Syntax_Syntax.U_succ uu____1864
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1868 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____1868
        | uu____1871 -> u2  in
      let uu____1872 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1872
  
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
                (let uu____1984 = norm_refinement env t12  in
                 match uu____1984 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2001;
                     FStar_Syntax_Syntax.vars = uu____2002;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2028 =
                       let uu____2029 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____2030 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2029 uu____2030
                        in
                     failwith uu____2028)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____2046 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____2046
          | FStar_Syntax_Syntax.Tm_uinst uu____2047 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2084 =
                   let uu____2085 = FStar_Syntax_Subst.compress t1'  in
                   uu____2085.FStar_Syntax_Syntax.n  in
                 match uu____2084 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2102 -> aux true t1'
                 | uu____2109 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2124 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2155 =
                   let uu____2156 = FStar_Syntax_Subst.compress t1'  in
                   uu____2156.FStar_Syntax_Syntax.n  in
                 match uu____2155 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2173 -> aux true t1'
                 | uu____2180 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2195 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2240 =
                   let uu____2241 = FStar_Syntax_Subst.compress t1'  in
                   uu____2241.FStar_Syntax_Syntax.n  in
                 match uu____2240 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2258 -> aux true t1'
                 | uu____2265 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2280 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2295 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2310 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____2325 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____2340 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____2367 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____2398 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____2429 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____2456 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____2493 ->
              let uu____2500 =
                let uu____2501 = FStar_Syntax_Print.term_to_string t12  in
                let uu____2502 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2501 uu____2502
                 in
              failwith uu____2500
          | FStar_Syntax_Syntax.Tm_ascribed uu____2517 ->
              let uu____2544 =
                let uu____2545 = FStar_Syntax_Print.term_to_string t12  in
                let uu____2546 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2545 uu____2546
                 in
              failwith uu____2544
          | FStar_Syntax_Syntax.Tm_delayed uu____2561 ->
              let uu____2586 =
                let uu____2587 = FStar_Syntax_Print.term_to_string t12  in
                let uu____2588 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2587 uu____2588
                 in
              failwith uu____2586
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____2603 =
                let uu____2604 = FStar_Syntax_Print.term_to_string t12  in
                let uu____2605 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____2604 uu____2605
                 in
              failwith uu____2603
           in
        let uu____2620 = whnf env t1  in aux false uu____2620
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let normalize_refinement :
  'Auu____2642 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____2642 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
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
      let uu____2665 = base_and_refinement env t  in
      FStar_All.pipe_right uu____2665 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____2699 = FStar_Syntax_Syntax.null_bv t  in
    (uu____2699, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____2705 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____2705 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____2726 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____2726 with
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
  fun uu____2805  ->
    match uu____2805 with
    | (t_base,refopt) ->
        let uu____2832 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____2832 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____2864 =
      let uu____2867 =
        let uu____2870 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2893  ->
                  match uu____2893 with | (uu____2900,uu____2901,x) -> x))
           in
        FStar_List.append wl.attempting uu____2870  in
      FStar_List.map (wl_prob_to_string wl) uu____2867  in
    FStar_All.pipe_right uu____2864 (FStar_String.concat "\n\t")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2914 =
          let uu____2927 =
            let uu____2928 = FStar_Syntax_Subst.compress k  in
            uu____2928.FStar_Syntax_Syntax.n  in
          match uu____2927 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2981 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____2981)
              else
                (let uu____2995 = FStar_Syntax_Util.abs_formals t  in
                 match uu____2995 with
                 | (ys',t1,uu____3018) ->
                     let uu____3023 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____3023))
          | uu____3064 ->
              let uu____3065 =
                let uu____3076 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____3076)  in
              ((ys, t), uu____3065)
           in
        match uu____2914 with
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
                 let uu____3125 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____3125 c  in
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
            let uu____3153 = p_guard prob  in
            match uu____3153 with
            | (uu____3158,uv) ->
                ((let uu____3161 =
                    let uu____3162 = FStar_Syntax_Subst.compress uv  in
                    uu____3162.FStar_Syntax_Syntax.n  in
                  match uu____3161 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob  in
                      let phi1 = u_abs k bs phi  in
                      ((let uu____3194 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel")
                           in
                        if uu____3194
                        then
                          let uu____3195 =
                            FStar_Util.string_of_int (p_pid prob)  in
                          let uu____3196 =
                            FStar_Syntax_Print.term_to_string uv  in
                          let uu____3197 =
                            FStar_Syntax_Print.term_to_string phi1  in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____3195
                            uu____3196 uu____3197
                        else ());
                       def_check_closed (p_loc prob) "solve_prob'" phi1;
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____3200 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___123_3203 = wl  in
                  {
                    attempting = (uu___123_3203.attempting);
                    wl_deferred = (uu___123_3203.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___123_3203.defer_ok);
                    smt_ok = (uu___123_3203.smt_ok);
                    tcenv = (uu___123_3203.tcenv)
                  }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____3218 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck")
            in
         if uu____3218
         then
           let uu____3219 = FStar_Util.string_of_int pid  in
           let uu____3220 =
             let uu____3221 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____3221 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with %s\n" uu____3219 uu____3220
         else ());
        commit sol;
        (let uu___124_3228 = wl  in
         {
           attempting = (uu___124_3228.attempting);
           wl_deferred = (uu___124_3228.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___124_3228.defer_ok);
           smt_ok = (uu___124_3228.smt_ok);
           tcenv = (uu___124_3228.tcenv)
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
            | (uu____3266,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____3278 = FStar_Syntax_Util.mk_conj t1 f  in
                FStar_Pervasives_Native.Some uu____3278
             in
          (let uu____3284 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck")
              in
           if uu____3284
           then
             let uu____3285 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____3286 =
               let uu____3287 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____3287 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____3285 uu____3286
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
        let uu____3319 =
          let uu____3326 = FStar_Syntax_Free.uvars t  in
          FStar_All.pipe_right uu____3326 FStar_Util.set_elements  in
        FStar_All.pipe_right uu____3319
          (FStar_Util.for_some
             (fun uu____3362  ->
                match uu____3362 with
                | (uv,uu____3368) ->
                    FStar_Syntax_Unionfind.equiv uv
                      (FStar_Pervasives_Native.fst uk)))
  
let occurs_check :
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
            let uu____3408 = occurs wl uk t  in Prims.op_Negation uu____3408
             in
          let msg =
            if occurs_ok
            then FStar_Pervasives_Native.None
            else
              (let uu____3415 =
                 let uu____3416 =
                   FStar_Syntax_Print.uvar_to_string
                     (FStar_Pervasives_Native.fst uk)
                    in
                 let uu____3417 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____3416 uu____3417
                  in
               FStar_Pervasives_Native.Some uu____3415)
             in
          (occurs_ok, msg)
  
let occurs_and_freevars_check :
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
            let fvs_t = FStar_Syntax_Free.names t  in
            let uu____3482 = occurs_check env wl uk t  in
            match uu____3482 with
            | (occurs_ok,msg) ->
                let uu____3513 = FStar_Util.set_is_subset_of fvs_t fvs  in
                (occurs_ok, uu____3513, (msg, fvs, fvs_t))
  
let intersect_vars :
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
             FStar_Syntax_Syntax.no_names)
         in
      let v1_set = as_set1 v1  in
      let uu____3621 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____3675  ->
                fun uu____3676  ->
                  match (uu____3675, uu____3676) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____3757 =
                        let uu____3758 = FStar_Util.set_mem x v1_set  in
                        FStar_All.pipe_left Prims.op_Negation uu____3758  in
                      if uu____3757
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort
                            in
                         let uu____3783 =
                           FStar_Util.set_is_subset_of fvs isect_set  in
                         if uu____3783
                         then
                           let uu____3796 = FStar_Util.set_add x isect_set
                              in
                           (((x, imp) :: isect), uu____3796)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names))
         in
      match uu____3621 with | (isect,uu____3837) -> FStar_List.rev isect
  
let binders_eq :
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
  
let pat_var_opt :
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
        let hd1 = norm_arg env arg  in
        match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_name a ->
            let uu____4005 =
              FStar_All.pipe_right seen
                (FStar_Util.for_some
                   (fun uu____4019  ->
                      match uu____4019 with
                      | (b,uu____4025) -> FStar_Syntax_Syntax.bv_eq a b))
               in
            if uu____4005
            then FStar_Pervasives_Native.None
            else
              FStar_Pervasives_Native.Some
                (a, (FStar_Pervasives_Native.snd hd1))
        | uu____4041 -> FStar_Pervasives_Native.None
  
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
            let uu____4114 = pat_var_opt env seen hd1  in
            (match uu____4114 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____4128 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel")
                      in
                   if uu____4128
                   then
                     let uu____4129 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1)
                        in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____4129
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4147 =
      let uu____4148 = FStar_Syntax_Subst.compress t  in
      uu____4148.FStar_Syntax_Syntax.n  in
    match uu____4147 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4151 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____4168;
           FStar_Syntax_Syntax.pos = uu____4169;
           FStar_Syntax_Syntax.vars = uu____4170;_},uu____4171)
        -> true
    | uu____4208 -> false
  
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
           FStar_Syntax_Syntax.pos = uu____4332;
           FStar_Syntax_Syntax.vars = uu____4333;_},args)
        -> (t, uv, k, args)
    | uu____4401 -> failwith "Not a flex-uvar"
  
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
      let uu____4478 = destruct_flex_t t  in
      match uu____4478 with
      | (t1,uv,k,args) ->
          let uu____4593 = pat_vars env [] args  in
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
  | FullMatch [@@deriving show]
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____4772 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____4807 -> false
  
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____4811 -> false
  
let (head_match : match_result -> match_result) =
  fun uu___99_4814  ->
    match uu___99_4814 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____4829 -> HeadMatch
  
let (and_match :
  match_result -> (Prims.unit -> match_result) -> match_result) =
  fun m1  ->
    fun m2  ->
      match m1 with
      | MisMatch (i,j) -> MisMatch (i, j)
      | HeadMatch  ->
          let uu____4855 = m2 ()  in
          (match uu____4855 with
           | MisMatch (i,j) -> MisMatch (i, j)
           | uu____4870 -> HeadMatch)
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
            ((env.FStar_TypeChecker_Env.curmodule).FStar_Ident.str =
               ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr)
              && (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface)
          then d
          else FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____4879 ->
          let uu____4880 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____4880 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____4891 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____4910 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____4919 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____4947 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____4947
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____4948 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____4949 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____4950 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____4967 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____4980 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5004) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5010,uu____5011) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5053) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5074;
             FStar_Syntax_Syntax.index = uu____5075;
             FStar_Syntax_Syntax.sort = t2;_},uu____5077)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5084 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5085 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5086 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5099 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5117 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____5117
  
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
            let uu____5144 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____5144
            then FullMatch
            else
              (let uu____5146 =
                 let uu____5155 =
                   let uu____5158 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____5158  in
                 let uu____5159 =
                   let uu____5162 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____5162  in
                 (uu____5155, uu____5159)  in
               MisMatch uu____5146)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5168),FStar_Syntax_Syntax.Tm_uinst (g,uu____5170)) ->
            let uu____5179 = head_matches env f g  in
            FStar_All.pipe_right uu____5179 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5182 = FStar_Const.eq_const c d  in
            if uu____5182
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5189),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5191)) ->
            let uu____5240 = FStar_Syntax_Unionfind.equiv uv uv'  in
            if uu____5240
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5247),FStar_Syntax_Syntax.Tm_refine (y,uu____5249)) ->
            let uu____5258 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5258 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5260),uu____5261) ->
            let uu____5266 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____5266 head_match
        | (uu____5267,FStar_Syntax_Syntax.Tm_refine (x,uu____5269)) ->
            let uu____5274 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5274 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5275,FStar_Syntax_Syntax.Tm_type
           uu____5276) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5277,FStar_Syntax_Syntax.Tm_arrow uu____5278) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            if (FStar_List.length bs1) = (FStar_List.length bs2)
            then
              let uu____5407 =
                let uu____5408 = FStar_List.zip bs1 bs2  in
                let uu____5443 = head_matches env t12 t22  in
                FStar_List.fold_right
                  (fun uu____5452  ->
                     fun a  ->
                       match uu____5452 with
                       | (b1,b2) ->
                           and_match a
                             (fun uu____5461  -> branch_matches env b1 b2))
                  uu____5408 uu____5443
                 in
              FStar_All.pipe_right uu____5407 head_match
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5468),FStar_Syntax_Syntax.Tm_app (head',uu____5470))
            ->
            let uu____5511 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____5511 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5513),uu____5514) ->
            let uu____5535 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____5535 head_match
        | (uu____5536,FStar_Syntax_Syntax.Tm_app (head1,uu____5538)) ->
            let uu____5559 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____5559 head_match
        | uu____5560 ->
            let uu____5565 =
              let uu____5574 = delta_depth_of_term env t11  in
              let uu____5577 = delta_depth_of_term env t21  in
              (uu____5574, uu____5577)  in
            MisMatch uu____5565

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
          | (uu____5629,uu____5630) -> false  in
        let uu____5639 = b1  in
        match uu____5639 with
        | (p1,w1,t1) ->
            let uu____5659 = b2  in
            (match uu____5659 with
             | (p2,w2,t2) ->
                 let uu____5679 = FStar_Syntax_Syntax.eq_pat p1 p2  in
                 if uu____5679
                 then
                   let uu____5680 =
                     (let uu____5683 = FStar_Syntax_Util.eq_tm t1 t2  in
                      uu____5683 = FStar_Syntax_Util.Equal) &&
                       (related_by
                          (fun t11  ->
                             fun t21  ->
                               let uu____5692 =
                                 FStar_Syntax_Util.eq_tm t11 t21  in
                               uu____5692 = FStar_Syntax_Util.Equal) w1 w2)
                      in
                   (if uu____5680
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
  'Auu____5708 .
    FStar_TypeChecker_Env.env ->
      'Auu____5708 ->
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
            let uu____5741 = FStar_Syntax_Util.head_and_args t  in
            match uu____5741 with
            | (head1,uu____5759) ->
                let uu____5780 =
                  let uu____5781 = FStar_Syntax_Util.un_uinst head1  in
                  uu____5781.FStar_Syntax_Syntax.n  in
                (match uu____5780 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5787 =
                       let uu____5788 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       FStar_All.pipe_right uu____5788 FStar_Option.isSome
                        in
                     if uu____5787
                     then
                       let uu____5807 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t
                          in
                       FStar_All.pipe_right uu____5807
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                     else FStar_Pervasives_Native.None
                 | uu____5811 -> FStar_Pervasives_Native.None)
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
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5914)
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5932 =
                     let uu____5941 = maybe_inline t11  in
                     let uu____5944 = maybe_inline t21  in
                     (uu____5941, uu____5944)  in
                   match uu____5932 with
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
                (uu____5981,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail r
                else
                  (let uu____5999 =
                     let uu____6008 = maybe_inline t11  in
                     let uu____6011 = maybe_inline t21  in
                     (uu____6008, uu____6011)  in
                   match uu____5999 with
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
                let uu____6054 = FStar_TypeChecker_Common.decr_delta_depth d1
                   in
                (match uu____6054 with
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
                let uu____6077 =
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
                (match uu____6077 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6101 -> fail r
            | uu____6110 -> success n_delta r t11 t21  in
          aux true (Prims.parse_int "0") t1 t2
  
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | C of FStar_Syntax_Syntax.comp [@@deriving show]
let (uu___is_T : tc -> Prims.bool) =
  fun projectee  -> match projectee with | T _0 -> true | uu____6143 -> false 
let (__proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | T _0 -> _0 
let (uu___is_C : tc -> Prims.bool) =
  fun projectee  -> match projectee with | C _0 -> true | uu____6179 -> false 
let (__proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp) =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list[@@deriving show]
let (tc_to_string : tc -> Prims.string) =
  fun uu___100_6191  ->
    match uu___100_6191 with
    | T (t,uu____6193) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
  
let (generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6209 = FStar_Syntax_Util.type_u ()  in
      match uu____6209 with
      | (t,uu____6215) ->
          let uu____6216 = new_uvar r binders t  in
          FStar_Pervasives_Native.fst uu____6216
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6227 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____6227 FStar_Pervasives_Native.fst
  
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
        let uu____6291 = head_matches env t1 t'  in
        match uu____6291 with
        | MisMatch uu____6292 -> false
        | uu____6301 -> true  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6397,imp),T (t2,uu____6400)) -> (t2, imp)
                     | uu____6419 -> failwith "Bad reconstruction") args
                args'
               in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6486  ->
                    match uu____6486 with
                    | (t2,uu____6500) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6543 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6543 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6618))::tcs2) ->
                       aux
                         (((let uu___125_6653 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___125_6653.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___125_6653.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6671 -> failwith "Bad reconstruction"  in
                 aux [] bs1 tcs  in
               let rec decompose1 out uu___101_6724 =
                 match uu___101_6724 with
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
               let uu____6841 = decompose1 [] bs1  in
               (rebuild, matches, uu____6841))
      | uu____6890 ->
          let rebuild uu___102_6896 =
            match uu___102_6896 with
            | [] -> t1
            | uu____6899 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
  
let (un_T : tc -> FStar_Syntax_Syntax.term) =
  fun uu___103_6930  ->
    match uu___103_6930 with
    | T (t,uu____6932) -> t
    | uu____6941 -> failwith "Impossible"
  
let (arg_of_tc : tc -> FStar_Syntax_Syntax.arg) =
  fun uu___104_6944  ->
    match uu___104_6944 with
    | T (t,uu____6946) -> FStar_Syntax_Syntax.as_arg t
    | uu____6955 -> failwith "Impossible"
  
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
              | (uu____7071,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r  in
                  let uu____7096 = new_uvar r scope1 k  in
                  (match uu____7096 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7114 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r
                          in
                       let uu____7131 =
                         let uu____7132 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm"
                            in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____7132
                          in
                       ((T (gi_xs, mk_kind)), uu____7131))
              | (uu____7145,uu____7146,C uu____7147) -> failwith "impos"  in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7294 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7311;
                         FStar_Syntax_Syntax.vars = uu____7312;_})
                        ->
                        let uu____7335 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____7335 with
                         | (T (gi_xs,uu____7359),prob) ->
                             let uu____7369 =
                               let uu____7370 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____7370
                                in
                             (uu____7369, [prob])
                         | uu____7373 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7388;
                         FStar_Syntax_Syntax.vars = uu____7389;_})
                        ->
                        let uu____7412 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____7412 with
                         | (T (gi_xs,uu____7436),prob) ->
                             let uu____7446 =
                               let uu____7447 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                                  in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____7447
                                in
                             (uu____7446, [prob])
                         | uu____7450 -> failwith "impossible")
                    | (uu____7461,uu____7462,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7464;
                         FStar_Syntax_Syntax.vars = uu____7465;_})
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
                        let uu____7596 =
                          let uu____7605 =
                            FStar_List.map (sub_prob scope1 args) components1
                             in
                          FStar_All.pipe_right uu____7605 FStar_List.unzip
                           in
                        (match uu____7596 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7659 =
                                 let uu____7660 =
                                   let uu____7663 = FStar_List.hd tcs  in
                                   FStar_All.pipe_right uu____7663 un_T  in
                                 let uu____7664 =
                                   let uu____7673 = FStar_List.tl tcs  in
                                   FStar_All.pipe_right uu____7673
                                     (FStar_List.map arg_of_tc)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7660;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7664;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 }  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7659
                                in
                             ((C gi_xs), sub_probs))
                    | uu____7682 ->
                        let uu____7695 = sub_prob scope1 args q  in
                        (match uu____7695 with
                         | (ktec,prob) -> (ktec, [prob]))
                     in
                  (match uu____7294 with
                   | (tc,probs) ->
                       let uu____7726 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7789,uu____7790),T
                            (t,uu____7792)) ->
                             let b1 =
                               ((let uu___126_7829 = b  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___126_7829.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___126_7829.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp)
                                in
                             let uu____7830 =
                               let uu____7837 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1
                                  in
                               uu____7837 :: args  in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7830)
                         | uu____7872 ->
                             (FStar_Pervasives_Native.None, scope1, args)
                          in
                       (match uu____7726 with
                        | (bopt,scope2,args1) ->
                            let uu____7956 = aux scope2 args1 qs2  in
                            (match uu____7956 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let f1 =
                                         let uu____7994 =
                                           let uu____7997 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           f :: uu____7997  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____7994
                                          in
                                       (def_check_closed (p_loc orig)
                                          "imitation_sub_probs (1)" f1;
                                        f1)
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                          in
                                       let f1 =
                                         let uu____8022 =
                                           let uu____8025 =
                                             FStar_Syntax_Util.mk_forall u_b
                                               (FStar_Pervasives_Native.fst b)
                                               f
                                              in
                                           let uu____8026 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           uu____8025 :: uu____8026  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8022
                                          in
                                       (def_check_closed (p_loc orig)
                                          "imitation_sub_probs (2)" f1;
                                        f1)
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
  'Auu____8095 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8095)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8095)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___127_8116 = p  in
      let uu____8121 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8122 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___127_8116.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8121;
        FStar_TypeChecker_Common.relation =
          (uu___127_8116.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8122;
        FStar_TypeChecker_Common.element =
          (uu___127_8116.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___127_8116.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___127_8116.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___127_8116.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___127_8116.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___127_8116.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8134 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____8134
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____8143 -> p
  
let (rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8163 = compress_prob wl pr  in
        FStar_All.pipe_right uu____8163 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8173 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8173 with
           | (lh,uu____8193) ->
               let uu____8214 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8214 with
                | (rh,uu____8234) ->
                    let uu____8255 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8272,FStar_Syntax_Syntax.Tm_uvar uu____8273)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8310,uu____8311)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8332,FStar_Syntax_Syntax.Tm_uvar uu____8333)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8354,uu____8355)
                          ->
                          let uu____8372 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____8372 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8421 ->
                                    let rank =
                                      let uu____8429 = is_top_level_prob prob
                                         in
                                      if uu____8429
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____8431 =
                                      let uu___128_8436 = tp  in
                                      let uu____8441 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___128_8436.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___128_8436.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___128_8436.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8441;
                                        FStar_TypeChecker_Common.element =
                                          (uu___128_8436.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___128_8436.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___128_8436.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___128_8436.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___128_8436.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___128_8436.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____8431)))
                      | (uu____8452,FStar_Syntax_Syntax.Tm_uvar uu____8453)
                          ->
                          let uu____8470 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____8470 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8519 ->
                                    let uu____8526 =
                                      let uu___129_8533 = tp  in
                                      let uu____8538 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___129_8533.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8538;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___129_8533.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___129_8533.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___129_8533.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___129_8533.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___129_8533.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___129_8533.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___129_8533.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___129_8533.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____8526)))
                      | (uu____8555,uu____8556) -> (rigid_rigid, tp)  in
                    (match uu____8255 with
                     | (rank,tp1) ->
                         let uu____8575 =
                           FStar_All.pipe_right
                             (let uu___130_8581 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___130_8581.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___130_8581.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___130_8581.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___130_8581.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___130_8581.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___130_8581.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___130_8581.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___130_8581.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___130_8581.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50)
                            in
                         (rank, uu____8575))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8591 =
            FStar_All.pipe_right
              (let uu___131_8597 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___131_8597.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___131_8597.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___131_8597.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___131_8597.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___131_8597.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___131_8597.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___131_8597.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___131_8597.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___131_8597.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51)
             in
          (rigid_rigid, uu____8591)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun wl  ->
    let rec aux uu____8652 probs =
      match uu____8652 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8705 = rank wl hd1  in
               (match uu____8705 with
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
    match projectee with | UDeferred _0 -> true | uu____8812 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8824 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8836 -> false
  
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
                        let uu____8876 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8876 with
                        | (k,uu____8882) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8892 -> false)))
            | uu____8893 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
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
                        let uu____8944 =
                          really_solve_universe_eq pid_orig wl1 u13 u23  in
                        (match uu____8944 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____8947 -> USolved wl1  in
                  aux wl us1 us2
                else
                  (let uu____8957 =
                     let uu____8958 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____8959 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____8958
                       uu____8959
                      in
                   UFailed uu____8957)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8979 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8979 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9001 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9001 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____9004 ->
                let uu____9009 =
                  let uu____9010 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____9011 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____9010
                    uu____9011 msg
                   in
                UFailed uu____9009
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9012,uu____9013) ->
              let uu____9014 =
                let uu____9015 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9016 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9015 uu____9016
                 in
              failwith uu____9014
          | (FStar_Syntax_Syntax.U_unknown ,uu____9017) ->
              let uu____9018 =
                let uu____9019 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9020 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9019 uu____9020
                 in
              failwith uu____9018
          | (uu____9021,FStar_Syntax_Syntax.U_bvar uu____9022) ->
              let uu____9023 =
                let uu____9024 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9025 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9024 uu____9025
                 in
              failwith uu____9023
          | (uu____9026,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9027 =
                let uu____9028 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9029 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9028 uu____9029
                 in
              failwith uu____9027
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9053 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____9053
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____9075 = occurs_univ v1 u3  in
              if uu____9075
              then
                let uu____9076 =
                  let uu____9077 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9078 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9077 uu____9078
                   in
                try_umax_components u11 u21 uu____9076
              else
                (let uu____9080 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9080)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____9100 = occurs_univ v1 u3  in
              if uu____9100
              then
                let uu____9101 =
                  let uu____9102 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9103 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9102 uu____9103
                   in
                try_umax_components u11 u21 uu____9101
              else
                (let uu____9105 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9105)
          | (FStar_Syntax_Syntax.U_max uu____9114,uu____9115) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9121 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9121
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9123,FStar_Syntax_Syntax.U_max uu____9124) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9130 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9130
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9132,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9133,FStar_Syntax_Syntax.U_name
             uu____9134) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9135) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9136) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9137,FStar_Syntax_Syntax.U_succ
             uu____9138) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9139,FStar_Syntax_Syntax.U_zero
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
      let uu____9225 = bc1  in
      match uu____9225 with
      | (bs1,mk_cod1) ->
          let uu____9266 = bc2  in
          (match uu____9266 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____9336 = FStar_Util.first_N n1 bs  in
                 match uu____9336 with
                 | (bs3,rest) ->
                     let uu____9361 = mk_cod rest  in (bs3, uu____9361)
                  in
               let l1 = FStar_List.length bs1  in
               let l2 = FStar_List.length bs2  in
               if l1 = l2
               then
                 let uu____9390 =
                   let uu____9397 = mk_cod1 []  in (bs1, uu____9397)  in
                 let uu____9400 =
                   let uu____9407 = mk_cod2 []  in (bs2, uu____9407)  in
                 (uu____9390, uu____9400)
               else
                 if l1 > l2
                 then
                   (let uu____9449 = curry l2 bs1 mk_cod1  in
                    let uu____9462 =
                      let uu____9469 = mk_cod2 []  in (bs2, uu____9469)  in
                    (uu____9449, uu____9462))
                 else
                   (let uu____9485 =
                      let uu____9492 = mk_cod1 []  in (bs1, uu____9492)  in
                    let uu____9495 = curry l1 bs2 mk_cod2  in
                    (uu____9485, uu____9495)))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____9616 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____9616
       then
         let uu____9617 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9617
       else ());
      (let uu____9619 = next_prob probs  in
       match uu____9619 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___132_9640 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___132_9640.wl_deferred);
               ctr = (uu___132_9640.ctr);
               defer_ok = (uu___132_9640.defer_ok);
               smt_ok = (uu___132_9640.smt_ok);
               tcenv = (uu___132_9640.tcenv)
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
                  let uu____9651 = solve_flex_rigid_join env tp probs1  in
                  (match uu____9651 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9656 = solve_rigid_flex_meet env tp probs1  in
                     match uu____9656 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9661,uu____9662) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9679 ->
                let uu____9688 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9747  ->
                          match uu____9747 with
                          | (c,uu____9755,uu____9756) -> c < probs.ctr))
                   in
                (match uu____9688 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9797 =
                            FStar_List.map
                              (fun uu____9812  ->
                                 match uu____9812 with
                                 | (uu____9823,x,y) -> (x, y))
                              probs.wl_deferred
                             in
                          Success uu____9797
                      | uu____9826 ->
                          let uu____9835 =
                            let uu___133_9836 = probs  in
                            let uu____9837 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9858  ->
                                      match uu____9858 with
                                      | (uu____9865,uu____9866,y) -> y))
                               in
                            {
                              attempting = uu____9837;
                              wl_deferred = rest;
                              ctr = (uu___133_9836.ctr);
                              defer_ok = (uu___133_9836.defer_ok);
                              smt_ok = (uu___133_9836.smt_ok);
                              tcenv = (uu___133_9836.tcenv)
                            }  in
                          solve env uu____9835))))

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
            let uu____9873 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____9873 with
            | USolved wl1 ->
                let uu____9875 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____9875
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
                  let uu____9921 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____9921 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9924 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9936;
                  FStar_Syntax_Syntax.vars = uu____9937;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9940;
                  FStar_Syntax_Syntax.vars = uu____9941;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9955,uu____9956) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9963,FStar_Syntax_Syntax.Tm_uinst uu____9964) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9971 -> USolved wl

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
            ((let uu____9981 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____9981
              then
                let uu____9982 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____9982 msg
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
        (let uu____9991 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____9991
         then
           let uu____9992 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____9992
         else ());
        (let uu____9994 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____9994 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____10056 = head_matches_delta env () t1 t2  in
               match uu____10056 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____10097 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____10146 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10161 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____10162 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____10161, uu____10162)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10167 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____10168 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____10167, uu____10168)
                           in
                        (match uu____10146 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____10194 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____10194
                                in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____10225 =
                                    let uu____10234 =
                                      let uu____10237 =
                                        let uu____10240 =
                                          let uu____10241 =
                                            let uu____10248 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2
                                               in
                                            (x, uu____10248)  in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____10241
                                           in
                                        FStar_Syntax_Syntax.mk uu____10240
                                         in
                                      uu____10237
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____10256 =
                                      let uu____10259 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort
                                         in
                                      [uu____10259]  in
                                    (uu____10234, uu____10256)  in
                                  FStar_Pervasives_Native.Some uu____10225
                              | (uu____10272,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10274)) ->
                                  let uu____10279 =
                                    let uu____10286 =
                                      let uu____10289 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11
                                         in
                                      [uu____10289]  in
                                    (t11, uu____10286)  in
                                  FStar_Pervasives_Native.Some uu____10279
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10299),uu____10300) ->
                                  let uu____10305 =
                                    let uu____10312 =
                                      let uu____10315 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21
                                         in
                                      [uu____10315]  in
                                    (t21, uu____10312)  in
                                  FStar_Pervasives_Native.Some uu____10305
                              | uu____10324 ->
                                  let uu____10329 =
                                    FStar_Syntax_Util.head_and_args t11  in
                                  (match uu____10329 with
                                   | (head1,uu____10353) ->
                                       let uu____10374 =
                                         let uu____10375 =
                                           FStar_Syntax_Util.un_uinst head1
                                            in
                                         uu____10375.FStar_Syntax_Syntax.n
                                          in
                                       (match uu____10374 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10386;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10388;_}
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
                                        | uu____10395 ->
                                            FStar_Pervasives_Native.None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10408) ->
                  let uu____10433 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___105_10459  ->
                            match uu___105_10459 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10466 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____10466 with
                                      | (u',uu____10482) ->
                                          let uu____10503 =
                                            let uu____10504 = whnf env u'  in
                                            uu____10504.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____10503 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10508) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10533 -> false))
                                 | uu____10534 -> false)
                            | uu____10537 -> false))
                     in
                  (match uu____10433 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10571 tps =
                         match uu____10571 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10619 =
                                    let uu____10628 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound uu____10628  in
                                  (match uu____10619 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10663 -> FStar_Pervasives_Native.None)
                          in
                       let uu____10672 =
                         let uu____10681 =
                           let uu____10688 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (uu____10688, [])  in
                         make_lower_bound uu____10681 lower_bounds  in
                       (match uu____10672 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10700 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____10700
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
                            ((let uu____10720 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____10720
                              then
                                let wl' =
                                  let uu___134_10722 = wl  in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___134_10722.wl_deferred);
                                    ctr = (uu___134_10722.ctr);
                                    defer_ok = (uu___134_10722.defer_ok);
                                    smt_ok = (uu___134_10722.smt_ok);
                                    tcenv = (uu___134_10722.tcenv)
                                  }  in
                                let uu____10723 = wl_to_string wl'  in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10723
                              else ());
                             (let uu____10725 =
                                solve_t env eq_prob
                                  (let uu___135_10727 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___135_10727.wl_deferred);
                                     ctr = (uu___135_10727.ctr);
                                     defer_ok = (uu___135_10727.defer_ok);
                                     smt_ok = (uu___135_10727.smt_ok);
                                     tcenv = (uu___135_10727.tcenv)
                                   })
                                 in
                              match uu____10725 with
                              | Success uu____10730 ->
                                  let wl1 =
                                    let uu___136_10732 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___136_10732.wl_deferred);
                                      ctr = (uu___136_10732.ctr);
                                      defer_ok = (uu___136_10732.defer_ok);
                                      smt_ok = (uu___136_10732.smt_ok);
                                      tcenv = (uu___136_10732.tcenv)
                                    }  in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1
                                     in
                                  let uu____10734 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds
                                     in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10739 -> FStar_Pervasives_Native.None))))
              | uu____10740 -> failwith "Impossible: Not a rigid-flex"))

and (solve_flex_rigid_join :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10749 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____10749
         then
           let uu____10750 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10750
         else ());
        (let uu____10752 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____10752 with
         | (u,args) ->
             let uu____10791 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____10791 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i  in
                  let base_types_match t1 t2 =
                    let uu____10832 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____10832 with
                    | (h1,args1) ->
                        let uu____10873 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____10873 with
                         | (h2,uu____10893) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____10920 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  if uu____10920
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____10938 =
                                          let uu____10941 =
                                            let uu____10942 =
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
                                                   _0_53) uu____10942
                                             in
                                          [uu____10941]  in
                                        FStar_Pervasives_Native.Some
                                          uu____10938))
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
                                       (let uu____10975 =
                                          let uu____10978 =
                                            let uu____10979 =
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
                                                   _0_54) uu____10979
                                             in
                                          [uu____10978]  in
                                        FStar_Pervasives_Native.Some
                                          uu____10975))
                                  else FStar_Pervasives_Native.None
                              | uu____10993 -> FStar_Pervasives_Native.None))
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
                             let uu____11083 =
                               let uu____11092 =
                                 let uu____11095 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21  in
                                 FStar_Syntax_Util.refine x1 uu____11095  in
                               (uu____11092, m1)  in
                             FStar_Pervasives_Native.Some uu____11083)
                    | (uu____11108,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____11110)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____11158),uu____11159) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____11206 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11259) ->
                       let uu____11284 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___106_11310  ->
                                 match uu___106_11310 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____11317 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____11317 with
                                           | (u',uu____11333) ->
                                               let uu____11354 =
                                                 let uu____11355 =
                                                   whnf env u'  in
                                                 uu____11355.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____11354 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11359) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11384 -> false))
                                      | uu____11385 -> false)
                                 | uu____11388 -> false))
                          in
                       (match uu____11284 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11426 tps =
                              match uu____11426 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11488 =
                                         let uu____11499 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound uu____11499  in
                                       (match uu____11488 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11550 ->
                                       FStar_Pervasives_Native.None)
                               in
                            let uu____11561 =
                              let uu____11572 =
                                let uu____11581 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (uu____11581, [])  in
                              make_upper_bound uu____11572 upper_bounds  in
                            (match uu____11561 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11595 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____11595
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
                                 ((let uu____11621 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____11621
                                   then
                                     let wl' =
                                       let uu___137_11623 = wl  in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___137_11623.wl_deferred);
                                         ctr = (uu___137_11623.ctr);
                                         defer_ok = (uu___137_11623.defer_ok);
                                         smt_ok = (uu___137_11623.smt_ok);
                                         tcenv = (uu___137_11623.tcenv)
                                       }  in
                                     let uu____11624 = wl_to_string wl'  in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11624
                                   else ());
                                  (let uu____11626 =
                                     solve_t env eq_prob
                                       (let uu___138_11628 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___138_11628.wl_deferred);
                                          ctr = (uu___138_11628.ctr);
                                          defer_ok =
                                            (uu___138_11628.defer_ok);
                                          smt_ok = (uu___138_11628.smt_ok);
                                          tcenv = (uu___138_11628.tcenv)
                                        })
                                      in
                                   match uu____11626 with
                                   | Success uu____11631 ->
                                       let wl1 =
                                         let uu___139_11633 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___139_11633.wl_deferred);
                                           ctr = (uu___139_11633.ctr);
                                           defer_ok =
                                             (uu___139_11633.defer_ok);
                                           smt_ok = (uu___139_11633.smt_ok);
                                           tcenv = (uu___139_11633.tcenv)
                                         }  in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1
                                          in
                                       let uu____11635 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds
                                          in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11640 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11641 -> failwith "Impossible: Not a flex-rigid")))

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
                    ((let uu____11716 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____11716
                      then
                        let uu____11717 = prob_to_string env1 rhs_prob  in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11717
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst
                         in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___140_11771 = hd1  in
                      let uu____11772 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___140_11771.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___140_11771.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11772
                      }  in
                    let hd21 =
                      let uu___141_11776 = hd2  in
                      let uu____11777 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___141_11776.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___141_11776.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11777
                      }  in
                    let prob =
                      let uu____11781 =
                        let uu____11786 =
                          FStar_All.pipe_left invert_rel (p_rel orig)  in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11786 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter"
                         in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____11781
                       in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                    let subst2 =
                      let uu____11797 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1
                         in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11797
                       in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                    let uu____11801 =
                      aux (FStar_List.append scope [(hd12, imp)]) env2 subst2
                        xs1 ys1
                       in
                    (match uu____11801 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11839 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst
                              in
                           let uu____11844 =
                             close_forall env2 [(hd12, imp)] phi  in
                           FStar_Syntax_Util.mk_conj uu____11839 uu____11844
                            in
                         ((let uu____11854 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____11854
                           then
                             let uu____11855 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____11856 =
                               FStar_Syntax_Print.bv_to_string hd12  in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11855 uu____11856
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11879 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch"
                 in
              let scope = p_scope orig  in
              let uu____11889 = aux scope env [] bs1 bs2  in
              match uu____11889 with
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
        let uu____11913 = compress_tprob wl problem  in
        solve_t' env uu____11913 wl

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____11946 = head_matches_delta env1 wl1 t1 t2  in
          match uu____11946 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____11977,uu____11978) ->
                   let rec may_relate head3 =
                     let uu____12003 =
                       let uu____12004 = FStar_Syntax_Subst.compress head3
                          in
                       uu____12004.FStar_Syntax_Syntax.n  in
                     match uu____12003 with
                     | FStar_Syntax_Syntax.Tm_name uu____12007 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____12008 -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____12031;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_equational ;
                           FStar_Syntax_Syntax.fv_qual = uu____12032;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____12035;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_abstract uu____12036;
                           FStar_Syntax_Syntax.fv_qual = uu____12037;_}
                         ->
                         problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____12041,uu____12042) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____12084) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____12090) ->
                         may_relate t
                     | uu____12095 -> false  in
                   let uu____12096 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok
                      in
                   if uu____12096
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
                                let uu____12113 =
                                  let uu____12114 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____12114 t21
                                   in
                                FStar_Syntax_Util.mk_forall u_x x uu____12113
                             in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1)
                        in
                     let uu____12116 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1
                        in
                     solve env1 uu____12116
                   else
                     (let uu____12118 =
                        let uu____12119 =
                          FStar_Syntax_Print.term_to_string head1  in
                        let uu____12120 =
                          FStar_Syntax_Print.term_to_string head2  in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____12119 uu____12120
                         in
                      giveup env1 uu____12118 orig)
               | (uu____12121,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___142_12135 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___142_12135.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___142_12135.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___142_12135.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___142_12135.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___142_12135.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___142_12135.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___142_12135.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___142_12135.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____12136,FStar_Pervasives_Native.None ) ->
                   ((let uu____12148 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____12148
                     then
                       let uu____12149 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12150 = FStar_Syntax_Print.tag_of_term t1
                          in
                       let uu____12151 = FStar_Syntax_Print.term_to_string t2
                          in
                       let uu____12152 = FStar_Syntax_Print.tag_of_term t2
                          in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____12149
                         uu____12150 uu____12151 uu____12152
                     else ());
                    (let uu____12154 = FStar_Syntax_Util.head_and_args t1  in
                     match uu____12154 with
                     | (head11,args1) ->
                         let uu____12191 = FStar_Syntax_Util.head_and_args t2
                            in
                         (match uu____12191 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1  in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____12245 =
                                  let uu____12246 =
                                    FStar_Syntax_Print.term_to_string head11
                                     in
                                  let uu____12247 = args_to_string args1  in
                                  let uu____12248 =
                                    FStar_Syntax_Print.term_to_string head21
                                     in
                                  let uu____12249 = args_to_string args2  in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____12246 uu____12247 uu____12248
                                    uu____12249
                                   in
                                giveup env1 uu____12245 orig
                              else
                                (let uu____12251 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____12257 =
                                        FStar_Syntax_Util.eq_args args1 args2
                                         in
                                      uu____12257 = FStar_Syntax_Util.Equal)
                                    in
                                 if uu____12251
                                 then
                                   let uu____12258 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1
                                      in
                                   match uu____12258 with
                                   | USolved wl2 ->
                                       let uu____12260 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2
                                          in
                                       solve env1 uu____12260
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____12264 =
                                      base_and_refinement env1 t1  in
                                    match uu____12264 with
                                    | (base1,refinement1) ->
                                        let uu____12289 =
                                          base_and_refinement env1 t2  in
                                        (match uu____12289 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____12346 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1
                                                     in
                                                  (match uu____12346 with
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
                                                           (fun uu____12368 
                                                              ->
                                                              fun uu____12369
                                                                 ->
                                                                match 
                                                                  (uu____12368,
                                                                    uu____12369)
                                                                with
                                                                | ((a,uu____12387),
                                                                   (a',uu____12389))
                                                                    ->
                                                                    let uu____12398
                                                                    =
                                                                    let uu____12403
                                                                    =
                                                                    p_scope
                                                                    orig  in
                                                                    mk_problem
                                                                    uu____12403
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
                                                                    uu____12398)
                                                           args1 args2
                                                          in
                                                       let formula =
                                                         let uu____12409 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____12409
                                                          in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2
                                                          in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____12415 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1)
                                                     in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2)
                                                     in
                                                  solve_t env1
                                                    (let uu___143_12451 =
                                                       problem  in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___143_12451.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___143_12451.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___143_12451.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___143_12451.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___143_12451.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___143_12451.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___143_12451.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___143_12451.FStar_TypeChecker_Common.rank)
                                                     }) wl1))))))))
           in
        let force_quasi_pattern xs_opt uu____12484 =
          match uu____12484 with
          | (t,u,k,args) ->
              let debug1 f =
                let uu____12526 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12526 then f () else ()  in
              let rec aux pat_args pat_args_set pattern_vars pattern_var_set
                seen_formals formals res_t args1 =
                debug1
                  (fun uu____12622  ->
                     let uu____12623 =
                       FStar_Syntax_Print.binders_to_string ", " pat_args  in
                     FStar_Util.print1 "pat_args so far: {%s}\n" uu____12623);
                (match (formals, args1) with
                 | ([],[]) ->
                     let pat_args1 =
                       FStar_All.pipe_right (FStar_List.rev pat_args)
                         (FStar_List.map
                            (fun uu____12691  ->
                               match uu____12691 with
                               | (x,imp) ->
                                   let uu____12702 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   (uu____12702, imp)))
                        in
                     let pattern_vars1 = FStar_List.rev pattern_vars  in
                     let kk =
                       let uu____12715 = FStar_Syntax_Util.type_u ()  in
                       match uu____12715 with
                       | (t1,uu____12721) ->
                           let uu____12722 =
                             new_uvar t1.FStar_Syntax_Syntax.pos
                               pattern_vars1 t1
                              in
                           FStar_Pervasives_Native.fst uu____12722
                        in
                     let uu____12727 =
                       new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk
                        in
                     (match uu____12727 with
                      | (t',tm_u1) ->
                          let uu____12740 = destruct_flex_t t'  in
                          (match uu____12740 with
                           | (uu____12777,u1,k1,uu____12780) ->
                               let all_formals = FStar_List.rev seen_formals
                                  in
                               let k2 =
                                 let uu____12839 =
                                   FStar_Syntax_Syntax.mk_Total res_t  in
                                 FStar_Syntax_Util.arrow all_formals
                                   uu____12839
                                  in
                               let sol =
                                 let uu____12843 =
                                   let uu____12852 = u_abs k2 all_formals t'
                                      in
                                   ((u, k2), uu____12852)  in
                                 TERM uu____12843  in
                               let t_app =
                                 FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                   pat_args1 FStar_Pervasives_Native.None
                                   t.FStar_Syntax_Syntax.pos
                                  in
                               FStar_Pervasives_Native.Some
                                 (sol, (t_app, u1, k1, pat_args1))))
                 | (formal::formals1,hd1::tl1) ->
                     (debug1
                        (fun uu____12987  ->
                           let uu____12988 =
                             FStar_Syntax_Print.binder_to_string formal  in
                           let uu____12989 =
                             FStar_Syntax_Print.args_to_string [hd1]  in
                           FStar_Util.print2
                             "force_quasi_pattern (case 2): formal=%s, hd=%s\n"
                             uu____12988 uu____12989);
                      (let uu____13002 = pat_var_opt env pat_args hd1  in
                       match uu____13002 with
                       | FStar_Pervasives_Native.None  ->
                           (debug1
                              (fun uu____13022  ->
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
                                      (fun uu____13065  ->
                                         match uu____13065 with
                                         | (x,uu____13071) ->
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
                                (fun uu____13086  ->
                                   let uu____13087 =
                                     FStar_Syntax_Print.args_to_string [hd1]
                                      in
                                   let uu____13100 =
                                     FStar_Syntax_Print.binder_to_string y
                                      in
                                   FStar_Util.print2
                                     "%s (var = %s) maybe pat\n" uu____13087
                                     uu____13100);
                              (let fvs =
                                 FStar_Syntax_Free.names
                                   (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort
                                  in
                               let uu____13104 =
                                 let uu____13105 =
                                   FStar_Util.set_is_subset_of fvs
                                     pat_args_set
                                    in
                                 Prims.op_Negation uu____13105  in
                               if uu____13104
                               then
                                 (debug1
                                    (fun uu____13117  ->
                                       let uu____13118 =
                                         let uu____13121 =
                                           FStar_Syntax_Print.args_to_string
                                             [hd1]
                                            in
                                         let uu____13134 =
                                           let uu____13137 =
                                             FStar_Syntax_Print.binder_to_string
                                               y
                                              in
                                           let uu____13138 =
                                             let uu____13141 =
                                               FStar_Syntax_Print.term_to_string
                                                 (FStar_Pervasives_Native.fst
                                                    y).FStar_Syntax_Syntax.sort
                                                in
                                             let uu____13142 =
                                               let uu____13145 =
                                                 names_to_string fvs  in
                                               let uu____13146 =
                                                 let uu____13149 =
                                                   names_to_string
                                                     pattern_var_set
                                                    in
                                                 [uu____13149]  in
                                               uu____13145 :: uu____13146  in
                                             uu____13141 :: uu____13142  in
                                           uu____13137 :: uu____13138  in
                                         uu____13121 :: uu____13134  in
                                       FStar_Util.print
                                         "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n"
                                         uu____13118);
                                  aux pat_args pat_args_set pattern_vars
                                    pattern_var_set (formal :: seen_formals)
                                    formals1 res_t tl1)
                               else
                                 (let uu____13151 =
                                    FStar_Util.set_add
                                      (FStar_Pervasives_Native.fst y)
                                      pat_args_set
                                     in
                                  let uu____13154 =
                                    FStar_Util.set_add
                                      (FStar_Pervasives_Native.fst formal)
                                      pattern_var_set
                                     in
                                  aux (y :: pat_args) uu____13151 (formal ::
                                    pattern_vars) uu____13154 (formal ::
                                    seen_formals) formals1 res_t tl1)))))
                 | ([],uu____13161::uu____13162) ->
                     let uu____13193 =
                       let uu____13206 =
                         FStar_TypeChecker_Normalize.unfold_whnf env res_t
                          in
                       FStar_Syntax_Util.arrow_formals uu____13206  in
                     (match uu____13193 with
                      | (more_formals,res_t1) ->
                          (match more_formals with
                           | [] -> FStar_Pervasives_Native.None
                           | uu____13245 ->
                               aux pat_args pat_args_set pattern_vars
                                 pattern_var_set seen_formals more_formals
                                 res_t1 args1))
                 | (uu____13252::uu____13253,[]) ->
                     FStar_Pervasives_Native.None)
                 in
              let uu____13276 =
                let uu____13289 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k  in
                FStar_Syntax_Util.arrow_formals uu____13289  in
              (match uu____13276 with
               | (all_formals,res_t) ->
                   (debug1
                      (fun uu____13325  ->
                         let uu____13326 =
                           FStar_Syntax_Print.term_to_string t  in
                         let uu____13327 =
                           FStar_Syntax_Print.binders_to_string ", "
                             all_formals
                            in
                         let uu____13328 =
                           FStar_Syntax_Print.term_to_string res_t  in
                         let uu____13329 =
                           FStar_Syntax_Print.args_to_string args  in
                         FStar_Util.print4
                           "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n"
                           uu____13326 uu____13327 uu____13328 uu____13329);
                    (let uu____13330 = FStar_Syntax_Syntax.new_bv_set ()  in
                     let uu____13333 = FStar_Syntax_Syntax.new_bv_set ()  in
                     aux [] uu____13330 [] uu____13333 [] all_formals res_t
                       args)))
           in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____13367 = lhs  in
          match uu____13367 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____13377 ->
                    let uu____13378 = sn_binders env1 pat_vars1  in
                    u_abs k_uv uu____13378 rhs
                 in
              let wl2 =
                solve_prob orig FStar_Pervasives_Native.None
                  [TERM ((uv, k_uv), sol)] wl1
                 in
              solve env1 wl2
           in
        let imitate orig env1 wl1 p =
          let uu____13401 = p  in
          match uu____13401 with
          | (((u,k),xs,c),ps,(h,uu____13412,qs)) ->
              let xs1 = sn_binders env1 xs  in
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____13494 = imitation_sub_probs orig env1 xs1 ps qs  in
              (match uu____13494 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13517 = h gs_xs  in
                     let uu____13518 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57)
                        in
                     FStar_Syntax_Util.abs xs1 uu____13517 uu____13518  in
                   ((let uu____13524 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____13524
                     then
                       let uu____13525 =
                         let uu____13528 =
                           let uu____13529 =
                             FStar_List.map tc_to_string gs_xs  in
                           FStar_All.pipe_right uu____13529
                             (FStar_String.concat "\n\t>")
                            in
                         let uu____13534 =
                           let uu____13537 =
                             FStar_Syntax_Print.binders_to_string ", " xs1
                              in
                           let uu____13538 =
                             let uu____13541 =
                               FStar_Syntax_Print.comp_to_string c  in
                             let uu____13542 =
                               let uu____13545 =
                                 FStar_Syntax_Print.term_to_string im  in
                               let uu____13546 =
                                 let uu____13549 =
                                   FStar_Syntax_Print.tag_of_term im  in
                                 let uu____13550 =
                                   let uu____13553 =
                                     let uu____13554 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs
                                        in
                                     FStar_All.pipe_right uu____13554
                                       (FStar_String.concat ", ")
                                      in
                                   let uu____13559 =
                                     let uu____13562 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula
                                        in
                                     [uu____13562]  in
                                   uu____13553 :: uu____13559  in
                                 uu____13549 :: uu____13550  in
                               uu____13545 :: uu____13546  in
                             uu____13541 :: uu____13542  in
                           uu____13537 :: uu____13538  in
                         uu____13528 :: uu____13534  in
                       FStar_Util.print
                         "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13525
                     else ());
                    def_check_closed (p_loc orig) "imitate" im;
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1
                        in
                     solve env1 (attempt sub_probs wl2))))
           in
        let imitate' orig env1 wl1 uu___107_13584 =
          match uu___107_13584 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p  in
        let project orig env1 wl1 i p =
          let uu____13616 = p  in
          match uu____13616 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____13707 = FStar_List.nth ps i  in
              (match uu____13707 with
               | (pi,uu____13711) ->
                   let uu____13716 = FStar_List.nth xs i  in
                   (match uu____13716 with
                    | (xi,uu____13728) ->
                        let rec gs k =
                          let uu____13741 =
                            let uu____13754 =
                              FStar_TypeChecker_Normalize.unfold_whnf env1 k
                               in
                            FStar_Syntax_Util.arrow_formals uu____13754  in
                          match uu____13741 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____13829)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort
                                       in
                                    let uu____13842 = new_uvar r xs k_a  in
                                    (match uu____13842 with
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
                                         let uu____13864 = aux subst2 tl1  in
                                         (match uu____13864 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____13891 =
                                                let uu____13894 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1
                                                   in
                                                uu____13894 :: gi_xs'  in
                                              let uu____13895 =
                                                let uu____13898 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps
                                                   in
                                                uu____13898 :: gi_ps'  in
                                              (uu____13891, uu____13895)))
                                 in
                              aux [] bs
                           in
                        let uu____13903 =
                          let uu____13904 = matches pi  in
                          FStar_All.pipe_left Prims.op_Negation uu____13904
                           in
                        if uu____13903
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____13908 = gs xi.FStar_Syntax_Syntax.sort
                              in
                           match uu____13908 with
                           | (g_xs,uu____13920) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                  in
                               let proj =
                                 let uu____13931 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r
                                    in
                                 let uu____13932 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_58  ->
                                        FStar_Pervasives_Native.Some _0_58)
                                    in
                                 FStar_Syntax_Util.abs xs uu____13931
                                   uu____13932
                                  in
                               let sub1 =
                                 let uu____13938 =
                                   let uu____13943 = p_scope orig  in
                                   let uu____13944 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r
                                      in
                                   let uu____13947 =
                                     let uu____13950 =
                                       FStar_List.map
                                         (fun uu____13965  ->
                                            match uu____13965 with
                                            | (uu____13974,uu____13975,y) ->
                                                y) qs
                                        in
                                     FStar_All.pipe_left h uu____13950  in
                                   mk_problem uu____13943 orig uu____13944
                                     (p_rel orig) uu____13947
                                     FStar_Pervasives_Native.None
                                     "projection"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____13938
                                  in
                               ((let uu____13990 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13990
                                 then
                                   let uu____13991 =
                                     FStar_Syntax_Print.term_to_string proj
                                      in
                                   let uu____13992 = prob_to_string env1 sub1
                                      in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____13991 uu____13992
                                 else ());
                                (let wl2 =
                                   let uu____13995 =
                                     let uu____13998 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1)
                                        in
                                     FStar_Pervasives_Native.Some uu____13998
                                      in
                                   solve_prob orig uu____13995
                                     [TERM (u, proj)] wl1
                                    in
                                 let uu____14007 =
                                   solve env1 (attempt [sub1] wl2)  in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____14007)))))
           in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____14038 = lhs  in
          match uu____14038 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____14074 = FStar_Syntax_Util.arrow_formals_comp k_uv
                   in
                match uu____14074 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____14107 =
                        let uu____14154 = decompose env t2  in
                        (((uv, k_uv), xs, c), ps, uu____14154)  in
                      FStar_Pervasives_Native.Some uu____14107
                    else
                      (let rec elim k args =
                         let k1 =
                           FStar_TypeChecker_Normalize.unfold_whnf env k  in
                         let uu____14298 =
                           let uu____14305 =
                             let uu____14306 = FStar_Syntax_Subst.compress k1
                                in
                             uu____14306.FStar_Syntax_Syntax.n  in
                           (uu____14305, args)  in
                         match uu____14298 with
                         | (uu____14317,[]) ->
                             let uu____14320 =
                               let uu____14331 =
                                 FStar_Syntax_Syntax.mk_Total k1  in
                               ([], uu____14331)  in
                             FStar_Pervasives_Native.Some uu____14320
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____14352,uu____14353) ->
                             let uu____14374 =
                               FStar_Syntax_Util.head_and_args k1  in
                             (match uu____14374 with
                              | (uv1,uv_args) ->
                                  let uu____14417 =
                                    let uu____14418 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____14418.FStar_Syntax_Syntax.n  in
                                  (match uu____14417 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14428) ->
                                       let uu____14453 =
                                         pat_vars env [] uv_args  in
                                       (match uu____14453 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14480  ->
                                                      let uu____14481 =
                                                        let uu____14482 =
                                                          let uu____14483 =
                                                            let uu____14488 =
                                                              let uu____14489
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____14489
                                                                FStar_Pervasives_Native.fst
                                                               in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14488
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14483
                                                           in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14482
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14481))
                                               in
                                            let c1 =
                                              let uu____14499 =
                                                let uu____14500 =
                                                  let uu____14505 =
                                                    let uu____14506 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____14506
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14505
                                                   in
                                                FStar_Pervasives_Native.fst
                                                  uu____14500
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14499
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____14519 =
                                                let uu____14522 =
                                                  let uu____14523 =
                                                    let uu____14526 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____14526
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14523
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____14522
                                                 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14519
                                               in
                                            (def_check_closed (p_loc orig)
                                               "solve_t_flex_rigid.subterms"
                                               uv_sol;
                                             FStar_Syntax_Util.set_uvar uvar
                                               uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14545 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14550,uu____14551) ->
                             let uu____14570 =
                               FStar_Syntax_Util.head_and_args k1  in
                             (match uu____14570 with
                              | (uv1,uv_args) ->
                                  let uu____14613 =
                                    let uu____14614 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____14614.FStar_Syntax_Syntax.n  in
                                  (match uu____14613 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14624) ->
                                       let uu____14649 =
                                         pat_vars env [] uv_args  in
                                       (match uu____14649 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14676  ->
                                                      let uu____14677 =
                                                        let uu____14678 =
                                                          let uu____14679 =
                                                            let uu____14684 =
                                                              let uu____14685
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____14685
                                                                FStar_Pervasives_Native.fst
                                                               in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14684
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14679
                                                           in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14678
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14677))
                                               in
                                            let c1 =
                                              let uu____14695 =
                                                let uu____14696 =
                                                  let uu____14701 =
                                                    let uu____14702 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____14702
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14701
                                                   in
                                                FStar_Pervasives_Native.fst
                                                  uu____14696
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14695
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____14715 =
                                                let uu____14718 =
                                                  let uu____14719 =
                                                    let uu____14722 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____14722
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14719
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____14718
                                                 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14715
                                               in
                                            (def_check_closed (p_loc orig)
                                               "solve_t_flex_rigid.subterms"
                                               uv_sol;
                                             FStar_Syntax_Util.set_uvar uvar
                                               uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14741 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____14748) ->
                             let n_args = FStar_List.length args  in
                             let n_xs = FStar_List.length xs1  in
                             if n_xs = n_args
                             then
                               let uu____14789 =
                                 FStar_Syntax_Subst.open_comp xs1 c1  in
                               FStar_All.pipe_right uu____14789
                                 (fun _0_61  ->
                                    FStar_Pervasives_Native.Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____14825 =
                                    FStar_Util.first_N n_xs args  in
                                  match uu____14825 with
                                  | (args1,rest) ->
                                      let uu____14854 =
                                        FStar_Syntax_Subst.open_comp xs1 c1
                                         in
                                      (match uu____14854 with
                                       | (xs2,c2) ->
                                           let uu____14867 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest
                                              in
                                           FStar_Util.bind_opt uu____14867
                                             (fun uu____14891  ->
                                                match uu____14891 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____14931 =
                                    FStar_Util.first_N n_args xs1  in
                                  match uu____14931 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k1.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____14999 =
                                        let uu____15004 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____15004
                                         in
                                      FStar_All.pipe_right uu____14999
                                        (fun _0_62  ->
                                           FStar_Pervasives_Native.Some _0_62))
                         | uu____15019 ->
                             let uu____15026 =
                               let uu____15031 =
                                 let uu____15032 =
                                   FStar_Syntax_Print.uvar_to_string uv  in
                                 let uu____15033 =
                                   FStar_Syntax_Print.term_to_string k1  in
                                 let uu____15034 =
                                   FStar_Syntax_Print.term_to_string k_uv  in
                                 FStar_Util.format3
                                   "Impossible: ill-typed application %s : %s\n\t%s"
                                   uu____15032 uu____15033 uu____15034
                                  in
                               (FStar_Errors.Fatal_IllTyped, uu____15031)  in
                             FStar_Errors.raise_error uu____15026
                               t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15041 = elim k_uv ps  in
                       FStar_Util.bind_opt uu____15041
                         (fun uu____15096  ->
                            match uu____15096 with
                            | (xs1,c1) ->
                                let uu____15145 =
                                  let uu____15186 = decompose env t2  in
                                  (((uv, k_uv), xs1, c1), ps, uu____15186)
                                   in
                                FStar_Pervasives_Native.Some uu____15145))
                 in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail uu____15307 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig
                   in
                let rec try_project st i =
                  if i >= n1
                  then fail ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                     let uu____15321 = project orig env wl1 i st  in
                     match uu____15321 with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some (Failed uu____15335) ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some sol -> sol)
                   in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt  in
                  let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                  let uu____15350 = imitate orig env wl1 st  in
                  match uu____15350 with
                  | Failed uu____15355 ->
                      (FStar_Syntax_Unionfind.rollback tx;
                       try_project st (Prims.parse_int "0"))
                  | sol -> sol
                else fail ()  in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____15386 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1  in
                match uu____15386 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let uu____15409 = forced_lhs_pattern  in
                    (match uu____15409 with
                     | (lhs_t,uu____15411,uu____15412,uu____15413) ->
                         ((let uu____15415 =
                             FStar_TypeChecker_Env.debug env
                               (FStar_Options.Other "Rel")
                              in
                           if uu____15415
                           then
                             let uu____15416 = lhs1  in
                             match uu____15416 with
                             | (t0,uu____15418,uu____15419,uu____15420) ->
                                 let uu____15421 = forced_lhs_pattern  in
                                 (match uu____15421 with
                                  | (t11,uu____15423,uu____15424,uu____15425)
                                      ->
                                      let uu____15426 =
                                        FStar_Syntax_Print.term_to_string t0
                                         in
                                      let uu____15427 =
                                        FStar_Syntax_Print.term_to_string t11
                                         in
                                      FStar_Util.print2
                                        "force_quasi_pattern succeeded, turning %s into %s\n"
                                        uu____15426 uu____15427)
                           else ());
                          (let rhs_vars = FStar_Syntax_Free.names rhs  in
                           let lhs_vars = FStar_Syntax_Free.names lhs_t  in
                           let uu____15435 =
                             FStar_Util.set_is_subset_of rhs_vars lhs_vars
                              in
                           if uu____15435
                           then
                             ((let uu____15437 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "Rel")
                                  in
                               if uu____15437
                               then
                                 let uu____15438 =
                                   FStar_Syntax_Print.term_to_string rhs  in
                                 let uu____15439 = names_to_string rhs_vars
                                    in
                                 let uu____15440 = names_to_string lhs_vars
                                    in
                                 FStar_Util.print3
                                   "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n"
                                   uu____15438 uu____15439 uu____15440
                               else ());
                              (let tx =
                                 FStar_Syntax_Unionfind.new_transaction ()
                                  in
                               let wl2 =
                                 extend_solution (p_pid orig) [sol] wl1  in
                               let uu____15444 =
                                 let uu____15445 =
                                   FStar_TypeChecker_Common.as_tprob orig  in
                                 solve_t env uu____15445 wl2  in
                               match uu____15444 with
                               | Failed uu____15446 ->
                                   (FStar_Syntax_Unionfind.rollback tx;
                                    imitate_or_project n1 lhs1 rhs stopt)
                               | sol1 -> sol1))
                           else
                             ((let uu____15455 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "Rel")
                                  in
                               if uu____15455
                               then
                                 FStar_Util.print_string
                                   "fvar check failed for quasi pattern ... im/proj\n"
                               else ());
                              imitate_or_project n1 lhs1 rhs stopt))))
                 in
              let check_head fvs1 t21 =
                let uu____15468 = FStar_Syntax_Util.head_and_args t21  in
                match uu____15468 with
                | (hd1,uu____15484) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15505 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15518 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15519 -> true
                     | uu____15536 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1  in
                         let uu____15540 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1  in
                         if uu____15540
                         then true
                         else
                           ((let uu____15543 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____15543
                             then
                               let uu____15544 = names_to_string fvs_hd  in
                               FStar_Util.print1 "Free variables are %s\n"
                                 uu____15544
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
                   let uu____15564 = occurs_check env wl1 (uv, k_uv) t21  in
                   (match uu____15564 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15577 =
                            let uu____15578 = FStar_Option.get msg  in
                            Prims.strcat "occurs-check failed: " uu____15578
                             in
                          giveup_or_defer1 orig uu____15577
                        else
                          (let uu____15580 =
                             FStar_Util.set_is_subset_of fvs2 fvs1  in
                           if uu____15580
                           then
                             let uu____15581 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
                                in
                             (if uu____15581
                              then
                                let uu____15582 = subterms args_lhs  in
                                imitate' orig env wl1 uu____15582
                              else
                                ((let uu____15587 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____15587
                                  then
                                    let uu____15588 =
                                      FStar_Syntax_Print.term_to_string t11
                                       in
                                    let uu____15589 = names_to_string fvs1
                                       in
                                    let uu____15590 = names_to_string fvs2
                                       in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15588 uu____15589 uu____15590
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
                               (let uu____15594 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21)
                                   in
                                if uu____15594
                                then
                                  ((let uu____15596 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____15596
                                    then
                                      let uu____15597 =
                                        FStar_Syntax_Print.term_to_string t11
                                         in
                                      let uu____15598 = names_to_string fvs1
                                         in
                                      let uu____15599 = names_to_string fvs2
                                         in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                        uu____15597 uu____15598 uu____15599
                                    else ());
                                   (let uu____15601 = subterms args_lhs  in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) lhs1 t21
                                      uu____15601))
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
                     (let uu____15612 =
                        let uu____15613 = FStar_Syntax_Free.names t1  in
                        check_head uu____15613 t2  in
                      if uu____15612
                      then
                        let n_args_lhs = FStar_List.length args_lhs  in
                        ((let uu____15624 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel")
                             in
                          if uu____15624
                          then
                            let uu____15625 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____15626 =
                              FStar_Util.string_of_int n_args_lhs  in
                            FStar_Util.print2
                              "Not a pattern (%s) ... (lhs has %s args)\n"
                              uu____15625 uu____15626
                          else ());
                         (let uu____15634 = subterms args_lhs  in
                          pattern_eq_imitate_or_project n_args_lhs
                            (FStar_Pervasives_Native.fst lhs) t2 uu____15634))
                      else giveup env "head-symbol is free" orig))
           in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let solve_both_pats wl1 uu____15711 uu____15712 r =
               match (uu____15711, uu____15712) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____15910 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys)
                      in
                   if uu____15910
                   then
                     let uu____15911 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1
                        in
                     solve env uu____15911
                   else
                     (let xs1 = sn_binders env xs  in
                      let ys1 = sn_binders env ys  in
                      let zs = intersect_vars xs1 ys1  in
                      (let uu____15935 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____15935
                       then
                         let uu____15936 =
                           FStar_Syntax_Print.binders_to_string ", " xs1  in
                         let uu____15937 =
                           FStar_Syntax_Print.binders_to_string ", " ys1  in
                         let uu____15938 =
                           FStar_Syntax_Print.binders_to_string ", " zs  in
                         let uu____15939 =
                           FStar_Syntax_Print.term_to_string k1  in
                         let uu____15940 =
                           FStar_Syntax_Print.term_to_string k2  in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____15936 uu____15937 uu____15938 uu____15939
                           uu____15940
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2  in
                         let args_len = FStar_List.length args  in
                         if xs_len = args_len
                         then
                           let uu____16000 =
                             FStar_Syntax_Util.subst_of_list xs2 args  in
                           FStar_Syntax_Subst.subst uu____16000 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____16014 =
                                FStar_Util.first_N args_len xs2  in
                              match uu____16014 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____16068 =
                                      FStar_Syntax_Syntax.mk_GTotal k  in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____16068
                                     in
                                  let uu____16071 =
                                    FStar_Syntax_Util.subst_of_list xs3 args
                                     in
                                  FStar_Syntax_Subst.subst uu____16071 k3)
                           else
                             (let uu____16075 =
                                let uu____16076 =
                                  FStar_Syntax_Print.term_to_string k  in
                                let uu____16077 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2
                                   in
                                let uu____16078 =
                                  FStar_Syntax_Print.args_to_string args  in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____16076 uu____16077 uu____16078
                                 in
                              failwith uu____16075)
                          in
                       let uu____16079 =
                         let uu____16086 =
                           let uu____16099 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1
                              in
                           FStar_Syntax_Util.arrow_formals uu____16099  in
                         match uu____16086 with
                         | (bs,k1') ->
                             let uu____16124 =
                               let uu____16137 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2
                                  in
                               FStar_Syntax_Util.arrow_formals uu____16137
                                in
                             (match uu____16124 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1  in
                                  let k2'_ys = subst_k k2' cs args2  in
                                  let sub_prob =
                                    let uu____16165 =
                                      let uu____16170 = p_scope orig  in
                                      mk_problem uu____16170 orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____16165
                                     in
                                  let uu____16175 =
                                    let uu____16180 =
                                      let uu____16181 =
                                        FStar_Syntax_Subst.compress k1'  in
                                      uu____16181.FStar_Syntax_Syntax.n  in
                                    let uu____16184 =
                                      let uu____16185 =
                                        FStar_Syntax_Subst.compress k2'  in
                                      uu____16185.FStar_Syntax_Syntax.n  in
                                    (uu____16180, uu____16184)  in
                                  (match uu____16175 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____16194,uu____16195) ->
                                       (k1'_xs, [sub_prob])
                                   | (uu____16198,FStar_Syntax_Syntax.Tm_type
                                      uu____16199) -> (k2'_ys, [sub_prob])
                                   | uu____16202 ->
                                       let uu____16207 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____16207 with
                                        | (t,uu____16219) ->
                                            let uu____16220 = new_uvar r zs t
                                               in
                                            (match uu____16220 with
                                             | (k_zs,uu____16232) ->
                                                 let kprob =
                                                   let uu____16234 =
                                                     let uu____16239 =
                                                       p_scope orig  in
                                                     mk_problem uu____16239
                                                       orig k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs
                                                       FStar_Pervasives_Native.None
                                                       "flex-flex kinding"
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_64  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_64) uu____16234
                                                    in
                                                 (k_zs, [sub_prob; kprob])))))
                          in
                       match uu____16079 with
                       | (k_u',sub_probs) ->
                           let uu____16252 =
                             let uu____16263 =
                               let uu____16264 = new_uvar r zs k_u'  in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____16264
                                in
                             let uu____16273 =
                               let uu____16276 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow xs1 uu____16276  in
                             let uu____16279 =
                               let uu____16282 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow ys1 uu____16282  in
                             (uu____16263, uu____16273, uu____16279)  in
                           (match uu____16252 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs  in
                                let uu____16301 =
                                  occurs_check env wl1 (u1, k1) sub1  in
                                (match uu____16301 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1)  in
                                        let uu____16320 =
                                          FStar_Syntax_Unionfind.equiv u1 u2
                                           in
                                        if uu____16320
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
                                           let uu____16324 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2
                                              in
                                           match uu____16324 with
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
             let solve_one_pat uu____16377 uu____16378 =
               match (uu____16377, uu____16378) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____16496 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____16496
                     then
                       let uu____16497 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____16498 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____16497 uu____16498
                     else ());
                    (let uu____16500 = FStar_Syntax_Unionfind.equiv u1 u2  in
                     if uu____16500
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16519  ->
                              fun uu____16520  ->
                                match (uu____16519, uu____16520) with
                                | ((a,uu____16538),(t21,uu____16540)) ->
                                    let uu____16549 =
                                      let uu____16554 = p_scope orig  in
                                      let uu____16555 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      mk_problem uu____16554 orig uu____16555
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index"
                                       in
                                    FStar_All.pipe_right uu____16549
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2
                          in
                       let guard =
                         let uu____16561 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____16561  in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl
                          in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2  in
                        let rhs_vars = FStar_Syntax_Free.names t21  in
                        let uu____16576 = occurs_check env wl (u1, k1) t21
                           in
                        match uu____16576 with
                        | (occurs_ok,uu____16584) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs  in
                            let uu____16592 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars)
                               in
                            if uu____16592
                            then
                              let sol =
                                let uu____16594 =
                                  let uu____16603 = u_abs k1 xs t21  in
                                  ((u1, k1), uu____16603)  in
                                TERM uu____16594  in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl
                                 in
                              solve env wl1
                            else
                              (let uu____16610 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok)
                                  in
                               if uu____16610
                               then
                                 let uu____16611 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2)
                                    in
                                 match uu____16611 with
                                 | FStar_Pervasives_Native.None  ->
                                     giveup_or_defer1 orig
                                       "flex-flex constraint"
                                 | FStar_Pervasives_Native.Some
                                     (sol,(uu____16635,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl
                                        in
                                     ((let uu____16661 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern")
                                          in
                                       if uu____16661
                                       then
                                         let uu____16662 =
                                           uvi_to_string env sol  in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16662
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16669 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint"))))
                in
             let uu____16671 = lhs  in
             match uu____16671 with
             | (t1,u1,k1,args1) ->
                 let uu____16676 = rhs  in
                 (match uu____16676 with
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
                       | uu____16716 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16726 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1)
                                 in
                              match uu____16726 with
                              | FStar_Pervasives_Native.None  ->
                                  giveup env
                                    "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                    orig
                              | FStar_Pervasives_Native.Some
                                  (sol,uu____16744) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl  in
                                  ((let uu____16751 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern")
                                       in
                                    if uu____16751
                                    then
                                      let uu____16752 = uvi_to_string env sol
                                         in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16752
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16759 ->
                                        giveup env "impossible" orig))))))
           in
        let orig = FStar_TypeChecker_Common.TProb problem  in
        let uu____16761 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs
           in
        if uu____16761
        then
          let uu____16762 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____16762
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs  in
           let t2 = problem.FStar_TypeChecker_Common.rhs  in
           let uu____16766 = FStar_Util.physical_equality t1 t2  in
           if uu____16766
           then
             let uu____16767 =
               solve_prob orig FStar_Pervasives_Native.None [] wl  in
             solve env uu____16767
           else
             ((let uu____16770 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck")
                  in
               if uu____16770
               then
                 let uu____16771 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid
                    in
                 FStar_Util.print1 "Attempting %s\n" uu____16771
               else ());
              (let r = FStar_TypeChecker_Env.get_range env  in
               let not_quote t =
                 let uu____16778 =
                   let uu____16779 = FStar_Syntax_Subst.compress t  in
                   uu____16779.FStar_Syntax_Syntax.n  in
                 match uu____16778 with
                 | FStar_Syntax_Syntax.Tm_meta
                     (uu____16782,FStar_Syntax_Syntax.Meta_quoted
                      uu____16783)
                     -> false
                 | uu____16794 -> true  in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_delayed uu____16795,uu____16796) ->
                   failwith "Impossible: terms were not compressed"
               | (uu____16821,FStar_Syntax_Syntax.Tm_delayed uu____16822) ->
                   failwith "Impossible: terms were not compressed"
               | (FStar_Syntax_Syntax.Tm_ascribed uu____16847,uu____16848) ->
                   let uu____16875 =
                     let uu___144_16876 = problem  in
                     let uu____16877 = FStar_Syntax_Util.unascribe t1  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___144_16876.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16877;
                       FStar_TypeChecker_Common.relation =
                         (uu___144_16876.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___144_16876.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___144_16876.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___144_16876.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___144_16876.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___144_16876.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___144_16876.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___144_16876.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____16875 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____16878,uu____16879) when
                   not_quote t1 ->
                   let uu____16886 =
                     let uu___145_16887 = problem  in
                     let uu____16888 = FStar_Syntax_Util.unmeta t1  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___145_16887.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16888;
                       FStar_TypeChecker_Common.relation =
                         (uu___145_16887.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___145_16887.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___145_16887.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___145_16887.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___145_16887.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___145_16887.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___145_16887.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___145_16887.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____16886 wl
               | (uu____16889,FStar_Syntax_Syntax.Tm_ascribed uu____16890) ->
                   let uu____16917 =
                     let uu___146_16918 = problem  in
                     let uu____16919 = FStar_Syntax_Util.unascribe t2  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___146_16918.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___146_16918.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___146_16918.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16919;
                       FStar_TypeChecker_Common.element =
                         (uu___146_16918.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___146_16918.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___146_16918.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___146_16918.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___146_16918.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___146_16918.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____16917 wl
               | (uu____16920,FStar_Syntax_Syntax.Tm_meta uu____16921) when
                   not_quote t2 ->
                   let uu____16928 =
                     let uu___147_16929 = problem  in
                     let uu____16930 = FStar_Syntax_Util.unmeta t2  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___147_16929.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___147_16929.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___147_16929.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____16930;
                       FStar_TypeChecker_Common.element =
                         (uu___147_16929.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___147_16929.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___147_16929.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___147_16929.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___147_16929.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___147_16929.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____16928 wl
               | (FStar_Syntax_Syntax.Tm_meta
                  (uu____16931,FStar_Syntax_Syntax.Meta_quoted
                   (t11,uu____16933)),FStar_Syntax_Syntax.Tm_meta
                  (uu____16934,FStar_Syntax_Syntax.Meta_quoted
                   (t21,uu____16936))) ->
                   let uu____16953 =
                     solve_prob orig FStar_Pervasives_Native.None [] wl  in
                   solve env uu____16953
               | (FStar_Syntax_Syntax.Tm_bvar uu____16954,uu____16955) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____16956,FStar_Syntax_Syntax.Tm_bvar uu____16957) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___108_17012 =
                     match uu___108_17012 with
                     | [] -> c
                     | bs ->
                         let uu____17034 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos
                            in
                         FStar_Syntax_Syntax.mk_Total uu____17034
                      in
                   let uu____17043 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                   (match uu____17043 with
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
                                   let uu____17185 =
                                     FStar_Options.use_eq_at_higher_order ()
                                      in
                                   if uu____17185
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation
                                    in
                                 let uu____17187 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____17187))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___109_17263 =
                     match uu___109_17263 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos
                      in
                   let uu____17297 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2))
                      in
                   (match uu____17297 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____17433 =
                                   let uu____17438 =
                                     FStar_Syntax_Subst.subst subst1 tbody11
                                      in
                                   let uu____17439 =
                                     FStar_Syntax_Subst.subst subst1 tbody21
                                      in
                                   mk_problem scope orig uu____17438
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____17439 FStar_Pervasives_Native.None
                                     "lambda co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____17433))
               | (FStar_Syntax_Syntax.Tm_abs uu____17444,uu____17445) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17470 -> true
                     | uu____17487 -> false  in
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
                       (let uu____17534 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___148_17542 = env  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___148_17542.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___148_17542.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___148_17542.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___148_17542.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___148_17542.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___148_17542.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___148_17542.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___148_17542.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___148_17542.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___148_17542.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___148_17542.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___148_17542.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___148_17542.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___148_17542.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___148_17542.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___148_17542.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___148_17542.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___148_17542.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___148_17542.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___148_17542.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___148_17542.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___148_17542.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___148_17542.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___148_17542.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___148_17542.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___148_17542.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___148_17542.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___148_17542.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___148_17542.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___148_17542.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___148_17542.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___148_17542.FStar_TypeChecker_Env.dep_graph)
                             }) t
                           in
                        match uu____17534 with
                        | (uu____17545,ty,uu____17547) ->
                            let uu____17548 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty
                               in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17548)
                      in
                   let uu____17549 =
                     let uu____17566 = maybe_eta t1  in
                     let uu____17573 = maybe_eta t2  in
                     (uu____17566, uu____17573)  in
                   (match uu____17549 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___149_17615 = problem  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___149_17615.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___149_17615.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___149_17615.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___149_17615.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___149_17615.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___149_17615.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___149_17615.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___149_17615.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17638 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____17638
                        then
                          let uu____17639 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____17639 t_abs wl
                        else
                          (let t11 = force_eta t1  in
                           let t21 = force_eta t2  in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___150_17654 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___150_17654.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___150_17654.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___150_17654.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___150_17654.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___150_17654.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___150_17654.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___150_17654.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___150_17654.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17678 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____17678
                        then
                          let uu____17679 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____17679 t_abs wl
                        else
                          (let t11 = force_eta t1  in
                           let t21 = force_eta t2  in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___150_17694 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___150_17694.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___150_17694.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___150_17694.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___150_17694.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___150_17694.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___150_17694.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___150_17694.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___150_17694.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17698 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17715,FStar_Syntax_Syntax.Tm_abs uu____17716) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17741 -> true
                     | uu____17758 -> false  in
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
                       (let uu____17805 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___148_17813 = env  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___148_17813.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___148_17813.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___148_17813.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___148_17813.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___148_17813.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___148_17813.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___148_17813.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___148_17813.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___148_17813.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___148_17813.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___148_17813.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___148_17813.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___148_17813.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___148_17813.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___148_17813.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___148_17813.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___148_17813.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___148_17813.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___148_17813.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___148_17813.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___148_17813.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___148_17813.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___148_17813.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___148_17813.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___148_17813.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___148_17813.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___148_17813.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___148_17813.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___148_17813.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___148_17813.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___148_17813.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___148_17813.FStar_TypeChecker_Env.dep_graph)
                             }) t
                           in
                        match uu____17805 with
                        | (uu____17816,ty,uu____17818) ->
                            let uu____17819 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty
                               in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17819)
                      in
                   let uu____17820 =
                     let uu____17837 = maybe_eta t1  in
                     let uu____17844 = maybe_eta t2  in
                     (uu____17837, uu____17844)  in
                   (match uu____17820 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___149_17886 = problem  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___149_17886.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___149_17886.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___149_17886.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___149_17886.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___149_17886.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___149_17886.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___149_17886.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___149_17886.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17909 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____17909
                        then
                          let uu____17910 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____17910 t_abs wl
                        else
                          (let t11 = force_eta t1  in
                           let t21 = force_eta t2  in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___150_17925 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___150_17925.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___150_17925.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___150_17925.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___150_17925.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___150_17925.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___150_17925.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___150_17925.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___150_17925.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17949 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____17949
                        then
                          let uu____17950 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____17950 t_abs wl
                        else
                          (let t11 = force_eta t1  in
                           let t21 = force_eta t2  in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___150_17965 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___150_17965.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___150_17965.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___150_17965.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___150_17965.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___150_17965.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___150_17965.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___150_17965.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___150_17965.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17969 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                   let should_delta =
                     ((let uu____18001 = FStar_Syntax_Free.uvars t1  in
                       FStar_Util.set_is_empty uu____18001) &&
                        (let uu____18013 = FStar_Syntax_Free.uvars t2  in
                         FStar_Util.set_is_empty uu____18013))
                       &&
                       (let uu____18028 =
                          head_matches env x1.FStar_Syntax_Syntax.sort
                            x2.FStar_Syntax_Syntax.sort
                           in
                        match uu____18028 with
                        | MisMatch
                            (FStar_Pervasives_Native.Some
                             d1,FStar_Pervasives_Native.Some d2)
                            ->
                            let is_unfoldable uu___110_18038 =
                              match uu___110_18038 with
                              | FStar_Syntax_Syntax.Delta_constant  -> true
                              | FStar_Syntax_Syntax.Delta_defined_at_level
                                  uu____18039 -> true
                              | uu____18040 -> false  in
                            (is_unfoldable d1) && (is_unfoldable d2)
                        | uu____18041 -> false)
                      in
                   let uu____18042 = as_refinement should_delta env wl t1  in
                   (match uu____18042 with
                    | (x11,phi1) ->
                        let uu____18049 =
                          as_refinement should_delta env wl t2  in
                        (match uu____18049 with
                         | (x21,phi21) ->
                             let base_prob =
                               let uu____18057 =
                                 let uu____18062 = p_scope orig  in
                                 mk_problem uu____18062 orig
                                   x11.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x21.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____18057
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
                                     let uu____18121 = p_scope orig  in
                                     let uu____18128 =
                                       let uu____18135 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____18135]  in
                                     FStar_List.append uu____18121
                                       uu____18128
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
                               let uu____18144 =
                                 solve env1
                                   (let uu___151_18146 = wl  in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___151_18146.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___151_18146.smt_ok);
                                      tcenv = (uu___151_18146.tcenv)
                                    })
                                  in
                               (match uu____18144 with
                                | Failed uu____18153 -> fallback ()
                                | Success uu____18158 ->
                                    let guard =
                                      let uu____18162 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      let uu____18167 =
                                        let uu____18168 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____18168
                                          (guard_on_element wl problem x12)
                                         in
                                      FStar_Syntax_Util.mk_conj uu____18162
                                        uu____18167
                                       in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl
                                       in
                                    let wl2 =
                                      let uu___152_18177 = wl1  in
                                      {
                                        attempting =
                                          (uu___152_18177.attempting);
                                        wl_deferred =
                                          (uu___152_18177.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___152_18177.defer_ok);
                                        smt_ok = (uu___152_18177.smt_ok);
                                        tcenv = (uu___152_18177.tcenv)
                                      }  in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18179,FStar_Syntax_Syntax.Tm_uvar uu____18180) ->
                   let uu____18213 = destruct_flex_t t1  in
                   let uu____18214 = destruct_flex_t t2  in
                   flex_flex1 orig uu____18213 uu____18214
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18215;
                     FStar_Syntax_Syntax.pos = uu____18216;
                     FStar_Syntax_Syntax.vars = uu____18217;_},uu____18218),FStar_Syntax_Syntax.Tm_uvar
                  uu____18219) ->
                   let uu____18272 = destruct_flex_t t1  in
                   let uu____18273 = destruct_flex_t t2  in
                   flex_flex1 orig uu____18272 uu____18273
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18274,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18275;
                     FStar_Syntax_Syntax.pos = uu____18276;
                     FStar_Syntax_Syntax.vars = uu____18277;_},uu____18278))
                   ->
                   let uu____18331 = destruct_flex_t t1  in
                   let uu____18332 = destruct_flex_t t2  in
                   flex_flex1 orig uu____18331 uu____18332
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18333;
                     FStar_Syntax_Syntax.pos = uu____18334;
                     FStar_Syntax_Syntax.vars = uu____18335;_},uu____18336),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18337;
                     FStar_Syntax_Syntax.pos = uu____18338;
                     FStar_Syntax_Syntax.vars = uu____18339;_},uu____18340))
                   ->
                   let uu____18413 = destruct_flex_t t1  in
                   let uu____18414 = destruct_flex_t t2  in
                   flex_flex1 orig uu____18413 uu____18414
               | (FStar_Syntax_Syntax.Tm_uvar uu____18415,uu____18416) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18433 = destruct_flex_pattern env t1  in
                   solve_t_flex_rigid false orig uu____18433 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18440;
                     FStar_Syntax_Syntax.pos = uu____18441;
                     FStar_Syntax_Syntax.vars = uu____18442;_},uu____18443),uu____18444)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18481 = destruct_flex_pattern env t1  in
                   solve_t_flex_rigid false orig uu____18481 t2 wl
               | (uu____18488,FStar_Syntax_Syntax.Tm_uvar uu____18489) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____18506,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18507;
                     FStar_Syntax_Syntax.pos = uu____18508;
                     FStar_Syntax_Syntax.vars = uu____18509;_},uu____18510))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18547,FStar_Syntax_Syntax.Tm_type uu____18548) ->
                   solve_t' env
                     (let uu___153_18566 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___153_18566.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___153_18566.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___153_18566.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___153_18566.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___153_18566.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___153_18566.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___153_18566.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___153_18566.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___153_18566.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18567;
                     FStar_Syntax_Syntax.pos = uu____18568;
                     FStar_Syntax_Syntax.vars = uu____18569;_},uu____18570),FStar_Syntax_Syntax.Tm_type
                  uu____18571) ->
                   solve_t' env
                     (let uu___153_18609 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___153_18609.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___153_18609.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___153_18609.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___153_18609.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___153_18609.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___153_18609.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___153_18609.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___153_18609.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___153_18609.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18610,FStar_Syntax_Syntax.Tm_arrow uu____18611) ->
                   solve_t' env
                     (let uu___153_18641 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___153_18641.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___153_18641.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___153_18641.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___153_18641.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___153_18641.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___153_18641.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___153_18641.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___153_18641.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___153_18641.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18642;
                     FStar_Syntax_Syntax.pos = uu____18643;
                     FStar_Syntax_Syntax.vars = uu____18644;_},uu____18645),FStar_Syntax_Syntax.Tm_arrow
                  uu____18646) ->
                   solve_t' env
                     (let uu___153_18696 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___153_18696.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___153_18696.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___153_18696.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___153_18696.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___153_18696.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___153_18696.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___153_18696.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___153_18696.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___153_18696.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18697,uu____18698) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation
                         in
                      let uu____18717 =
                        let uu____18718 = is_top_level_prob orig  in
                        FStar_All.pipe_left Prims.op_Negation uu____18718  in
                      if uu____18717
                      then
                        let uu____18719 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___154_18725 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___154_18725.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___154_18725.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___154_18725.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___154_18725.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___154_18725.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___154_18725.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___154_18725.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___154_18725.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___154_18725.FStar_TypeChecker_Common.rank)
                             })
                           in
                        let uu____18726 = destruct_flex_pattern env t1  in
                        solve_t_flex_rigid false uu____18719 uu____18726 t2
                          wl
                      else
                        (let uu____18734 = base_and_refinement env t2  in
                         match uu____18734 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18763 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___155_18769 = problem  in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___155_18769.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___155_18769.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___155_18769.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___155_18769.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___155_18769.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___155_18769.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___155_18769.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___155_18769.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___155_18769.FStar_TypeChecker_Common.rank)
                                       })
                                     in
                                  let uu____18770 =
                                    destruct_flex_pattern env t1  in
                                  solve_t_flex_rigid false uu____18763
                                    uu____18770 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___156_18784 = y  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___156_18784.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___156_18784.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }  in
                                  let impl =
                                    guard_on_element wl problem y' phi  in
                                  let base_prob =
                                    let uu____18787 =
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
                                      uu____18787
                                     in
                                  let guard =
                                    let uu____18799 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Util.mk_conj uu____18799
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
                       uu____18807;
                     FStar_Syntax_Syntax.pos = uu____18808;
                     FStar_Syntax_Syntax.vars = uu____18809;_},uu____18810),uu____18811)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation
                         in
                      let uu____18850 =
                        let uu____18851 = is_top_level_prob orig  in
                        FStar_All.pipe_left Prims.op_Negation uu____18851  in
                      if uu____18850
                      then
                        let uu____18852 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___154_18858 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___154_18858.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___154_18858.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___154_18858.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___154_18858.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___154_18858.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___154_18858.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___154_18858.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___154_18858.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___154_18858.FStar_TypeChecker_Common.rank)
                             })
                           in
                        let uu____18859 = destruct_flex_pattern env t1  in
                        solve_t_flex_rigid false uu____18852 uu____18859 t2
                          wl
                      else
                        (let uu____18867 = base_and_refinement env t2  in
                         match uu____18867 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18896 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___155_18902 = problem  in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___155_18902.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___155_18902.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___155_18902.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___155_18902.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___155_18902.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___155_18902.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___155_18902.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___155_18902.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___155_18902.FStar_TypeChecker_Common.rank)
                                       })
                                     in
                                  let uu____18903 =
                                    destruct_flex_pattern env t1  in
                                  solve_t_flex_rigid false uu____18896
                                    uu____18903 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___156_18917 = y  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___156_18917.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___156_18917.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }  in
                                  let impl =
                                    guard_on_element wl problem y' phi  in
                                  let base_prob =
                                    let uu____18920 =
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
                                      uu____18920
                                     in
                                  let guard =
                                    let uu____18932 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Util.mk_conj uu____18932
                                      impl
                                     in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl
                                     in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____18940,FStar_Syntax_Syntax.Tm_uvar uu____18941) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____18959 = base_and_refinement env t1  in
                      match uu____18959 with
                      | (t_base,uu____18971) ->
                          solve_t env
                            (let uu___157_18985 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___157_18985.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___157_18985.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___157_18985.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___157_18985.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___157_18985.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___157_18985.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___157_18985.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___157_18985.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____18986,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18987;
                     FStar_Syntax_Syntax.pos = uu____18988;
                     FStar_Syntax_Syntax.vars = uu____18989;_},uu____18990))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____19028 = base_and_refinement env t1  in
                      match uu____19028 with
                      | (t_base,uu____19040) ->
                          solve_t env
                            (let uu___157_19054 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___157_19054.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___157_19054.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___157_19054.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___157_19054.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___157_19054.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___157_19054.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___157_19054.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___157_19054.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____19055,uu____19056) ->
                   let t21 =
                     let uu____19066 = base_and_refinement env t2  in
                     FStar_All.pipe_left force_refinement uu____19066  in
                   solve_t env
                     (let uu___158_19090 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___158_19090.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___158_19090.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___158_19090.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___158_19090.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___158_19090.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___158_19090.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___158_19090.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___158_19090.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___158_19090.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____19091,FStar_Syntax_Syntax.Tm_refine uu____19092) ->
                   let t11 =
                     let uu____19102 = base_and_refinement env t1  in
                     FStar_All.pipe_left force_refinement uu____19102  in
                   solve_t env
                     (let uu___159_19126 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___159_19126.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___159_19126.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___159_19126.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___159_19126.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___159_19126.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___159_19126.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___159_19126.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___159_19126.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___159_19126.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____19129,uu____19130) ->
                   let head1 =
                     let uu____19156 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19156
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19200 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19200
                       FStar_Pervasives_Native.fst
                      in
                   let uu____19241 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____19241
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____19256 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____19256
                      then
                        let guard =
                          let uu____19268 =
                            let uu____19269 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____19269 = FStar_Syntax_Util.Equal  in
                          if uu____19268
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19273 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____19273)
                           in
                        let uu____19276 = solve_prob orig guard [] wl  in
                        solve env uu____19276
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____19279,uu____19280) ->
                   let head1 =
                     let uu____19290 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19290
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19334 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19334
                       FStar_Pervasives_Native.fst
                      in
                   let uu____19375 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____19375
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____19390 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____19390
                      then
                        let guard =
                          let uu____19402 =
                            let uu____19403 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____19403 = FStar_Syntax_Util.Equal  in
                          if uu____19402
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19407 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____19407)
                           in
                        let uu____19410 = solve_prob orig guard [] wl  in
                        solve env uu____19410
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____19413,uu____19414) ->
                   let head1 =
                     let uu____19418 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19418
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19462 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19462
                       FStar_Pervasives_Native.fst
                      in
                   let uu____19503 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____19503
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____19518 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____19518
                      then
                        let guard =
                          let uu____19530 =
                            let uu____19531 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____19531 = FStar_Syntax_Util.Equal  in
                          if uu____19530
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19535 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____19535)
                           in
                        let uu____19538 = solve_prob orig guard [] wl  in
                        solve env uu____19538
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____19541,uu____19542) ->
                   let head1 =
                     let uu____19546 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19546
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19590 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19590
                       FStar_Pervasives_Native.fst
                      in
                   let uu____19631 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____19631
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____19646 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____19646
                      then
                        let guard =
                          let uu____19658 =
                            let uu____19659 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____19659 = FStar_Syntax_Util.Equal  in
                          if uu____19658
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19663 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____19663)
                           in
                        let uu____19666 = solve_prob orig guard [] wl  in
                        solve env uu____19666
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____19669,uu____19670) ->
                   let head1 =
                     let uu____19674 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19674
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19718 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19718
                       FStar_Pervasives_Native.fst
                      in
                   let uu____19759 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____19759
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____19774 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____19774
                      then
                        let guard =
                          let uu____19786 =
                            let uu____19787 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____19787 = FStar_Syntax_Util.Equal  in
                          if uu____19786
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19791 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19791)
                           in
                        let uu____19794 = solve_prob orig guard [] wl  in
                        solve env uu____19794
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19797,uu____19798) ->
                   let head1 =
                     let uu____19816 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19816
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19860 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19860
                       FStar_Pervasives_Native.fst
                      in
                   let uu____19901 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____19901
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____19916 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____19916
                      then
                        let guard =
                          let uu____19928 =
                            let uu____19929 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____19929 = FStar_Syntax_Util.Equal  in
                          if uu____19928
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19933 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____19933)
                           in
                        let uu____19936 = solve_prob orig guard [] wl  in
                        solve env uu____19936
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____19939,FStar_Syntax_Syntax.Tm_match uu____19940) ->
                   let head1 =
                     let uu____19966 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19966
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20010 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20010
                       FStar_Pervasives_Native.fst
                      in
                   let uu____20051 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____20051
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____20066 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____20066
                      then
                        let guard =
                          let uu____20078 =
                            let uu____20079 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____20079 = FStar_Syntax_Util.Equal  in
                          if uu____20078
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20083 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____20083)
                           in
                        let uu____20086 = solve_prob orig guard [] wl  in
                        solve env uu____20086
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20089,FStar_Syntax_Syntax.Tm_uinst uu____20090) ->
                   let head1 =
                     let uu____20100 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20100
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20144 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20144
                       FStar_Pervasives_Native.fst
                      in
                   let uu____20185 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____20185
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____20200 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____20200
                      then
                        let guard =
                          let uu____20212 =
                            let uu____20213 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____20213 = FStar_Syntax_Util.Equal  in
                          if uu____20212
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20217 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____20217)
                           in
                        let uu____20220 = solve_prob orig guard [] wl  in
                        solve env uu____20220
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20223,FStar_Syntax_Syntax.Tm_name uu____20224) ->
                   let head1 =
                     let uu____20228 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20228
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20272 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20272
                       FStar_Pervasives_Native.fst
                      in
                   let uu____20313 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____20313
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____20328 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____20328
                      then
                        let guard =
                          let uu____20340 =
                            let uu____20341 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____20341 = FStar_Syntax_Util.Equal  in
                          if uu____20340
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20345 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____20345)
                           in
                        let uu____20348 = solve_prob orig guard [] wl  in
                        solve env uu____20348
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20351,FStar_Syntax_Syntax.Tm_constant uu____20352) ->
                   let head1 =
                     let uu____20356 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20356
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20400 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20400
                       FStar_Pervasives_Native.fst
                      in
                   let uu____20441 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____20441
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____20456 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____20456
                      then
                        let guard =
                          let uu____20468 =
                            let uu____20469 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____20469 = FStar_Syntax_Util.Equal  in
                          if uu____20468
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20473 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____20473)
                           in
                        let uu____20476 = solve_prob orig guard [] wl  in
                        solve env uu____20476
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20479,FStar_Syntax_Syntax.Tm_fvar uu____20480) ->
                   let head1 =
                     let uu____20484 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20484
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20528 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20528
                       FStar_Pervasives_Native.fst
                      in
                   let uu____20569 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____20569
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____20584 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____20584
                      then
                        let guard =
                          let uu____20596 =
                            let uu____20597 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____20597 = FStar_Syntax_Util.Equal  in
                          if uu____20596
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20601 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____20601)
                           in
                        let uu____20604 = solve_prob orig guard [] wl  in
                        solve env uu____20604
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20607,FStar_Syntax_Syntax.Tm_app uu____20608) ->
                   let head1 =
                     let uu____20626 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20626
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20670 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20670
                       FStar_Pervasives_Native.fst
                      in
                   let uu____20711 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____20711
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____20726 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____20726
                      then
                        let guard =
                          let uu____20738 =
                            let uu____20739 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____20739 = FStar_Syntax_Util.Equal  in
                          if uu____20738
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20743 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____20743)
                           in
                        let uu____20746 = solve_prob orig guard [] wl  in
                        solve env uu____20746
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let
                  uu____20749,FStar_Syntax_Syntax.Tm_let uu____20750) ->
                   let uu____20775 = FStar_Syntax_Util.term_eq t1 t2  in
                   if uu____20775
                   then
                     let uu____20776 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl  in
                     solve env uu____20776
                   else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
               | (FStar_Syntax_Syntax.Tm_let uu____20778,uu____20779) ->
                   let uu____20792 =
                     let uu____20797 =
                       let uu____20798 = FStar_Syntax_Print.tag_of_term t1
                          in
                       let uu____20799 = FStar_Syntax_Print.tag_of_term t2
                          in
                       let uu____20800 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____20801 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format4
                         "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                         uu____20798 uu____20799 uu____20800 uu____20801
                        in
                     (FStar_Errors.Fatal_UnificationNotWellFormed,
                       uu____20797)
                      in
                   FStar_Errors.raise_error uu____20792
                     t1.FStar_Syntax_Syntax.pos
               | (uu____20802,FStar_Syntax_Syntax.Tm_let uu____20803) ->
                   let uu____20816 =
                     let uu____20821 =
                       let uu____20822 = FStar_Syntax_Print.tag_of_term t1
                          in
                       let uu____20823 = FStar_Syntax_Print.tag_of_term t2
                          in
                       let uu____20824 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____20825 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format4
                         "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                         uu____20822 uu____20823 uu____20824 uu____20825
                        in
                     (FStar_Errors.Fatal_UnificationNotWellFormed,
                       uu____20821)
                      in
                   FStar_Errors.raise_error uu____20816
                     t1.FStar_Syntax_Syntax.pos
               | uu____20826 -> giveup env "head tag mismatch" orig)))

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
          let uu____20854 = p_scope orig  in
          mk_problem uu____20854 orig t1 rel t2 FStar_Pervasives_Native.None
            reason
           in
        let solve_eq c1_comp c2_comp =
          (let uu____20863 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____20863
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____20865 =
               let uu____20866 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____20867 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20866 uu____20867
                in
             giveup env uu____20865 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____20887  ->
                    fun uu____20888  ->
                      match (uu____20887, uu____20888) with
                      | ((a1,uu____20906),(a2,uu____20908)) ->
                          let uu____20917 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg"
                             in
                          FStar_All.pipe_left
                            (fun _0_88  ->
                               FStar_TypeChecker_Common.TProb _0_88)
                            uu____20917)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args
                in
             let guard =
               let uu____20927 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs
                  in
               FStar_Syntax_Util.mk_conj_l uu____20927  in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl  in
             solve env (attempt sub_probs wl1))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____20951 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20958)::[] -> wp1
              | uu____20975 ->
                  let uu____20984 =
                    let uu____20985 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name)
                       in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20985
                     in
                  failwith uu____20984
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____20993 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____20993]
              | x -> x  in
            let uu____20995 =
              let uu____21004 =
                let uu____21005 =
                  let uu____21006 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____21006 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____21005  in
              [uu____21004]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20995;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____21007 = lift_c1 ()  in solve_eq uu____21007 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___111_21013  ->
                       match uu___111_21013 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____21014 -> false))
                in
             let uu____21015 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____21049)::uu____21050,(wp2,uu____21052)::uu____21053)
                   -> (wp1, wp2)
               | uu____21110 ->
                   let uu____21131 =
                     let uu____21136 =
                       let uu____21137 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____21138 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____21137 uu____21138
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____21136)
                      in
                   FStar_Errors.raise_error uu____21131
                     env.FStar_TypeChecker_Env.range
                in
             match uu____21015 with
             | (wpc1,wpc2) ->
                 let uu____21157 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____21157
                 then
                   let uu____21160 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____21160 wl
                 else
                   (let uu____21164 =
                      let uu____21171 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____21171  in
                    match uu____21164 with
                    | (c2_decl,qualifiers) ->
                        let uu____21192 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____21192
                        then
                          let c1_repr =
                            let uu____21196 =
                              let uu____21197 =
                                let uu____21198 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____21198  in
                              let uu____21199 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21197 uu____21199
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21196
                             in
                          let c2_repr =
                            let uu____21201 =
                              let uu____21202 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____21203 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21202 uu____21203
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21201
                             in
                          let prob =
                            let uu____21205 =
                              let uu____21210 =
                                let uu____21211 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____21212 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____21211
                                  uu____21212
                                 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____21210
                               in
                            FStar_TypeChecker_Common.TProb uu____21205  in
                          let wl1 =
                            let uu____21214 =
                              let uu____21217 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_Pervasives_Native.Some uu____21217  in
                            solve_prob orig uu____21214 [] wl  in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____21226 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21226
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____21229 =
                                     let uu____21232 =
                                       let uu____21233 =
                                         let uu____21248 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____21249 =
                                           let uu____21252 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____21253 =
                                             let uu____21256 =
                                               let uu____21257 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____21257
                                                in
                                             [uu____21256]  in
                                           uu____21252 :: uu____21253  in
                                         (uu____21248, uu____21249)  in
                                       FStar_Syntax_Syntax.Tm_app uu____21233
                                        in
                                     FStar_Syntax_Syntax.mk uu____21232  in
                                   uu____21229 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____21266 =
                                    let uu____21269 =
                                      let uu____21270 =
                                        let uu____21285 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____21286 =
                                          let uu____21289 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____21290 =
                                            let uu____21293 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____21294 =
                                              let uu____21297 =
                                                let uu____21298 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____21298
                                                 in
                                              [uu____21297]  in
                                            uu____21293 :: uu____21294  in
                                          uu____21289 :: uu____21290  in
                                        (uu____21285, uu____21286)  in
                                      FStar_Syntax_Syntax.Tm_app uu____21270
                                       in
                                    FStar_Syntax_Syntax.mk uu____21269  in
                                  uu____21266 FStar_Pervasives_Native.None r)
                              in
                           let base_prob =
                             let uu____21305 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type"
                                in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____21305
                              in
                           let wl1 =
                             let uu____21315 =
                               let uu____21318 =
                                 let uu____21321 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____21321 g  in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____21318
                                in
                             solve_prob orig uu____21315 [] wl  in
                           solve env (attempt [base_prob] wl1))))
           in
        let uu____21334 = FStar_Util.physical_equality c1 c2  in
        if uu____21334
        then
          let uu____21335 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____21335
        else
          ((let uu____21338 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____21338
            then
              let uu____21339 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____21340 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____21339
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____21340
            else ());
           (let uu____21342 =
              let uu____21347 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____21348 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____21347, uu____21348)  in
            match uu____21342 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21352),FStar_Syntax_Syntax.Total
                    (t2,uu____21354)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21371 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21371 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21374,FStar_Syntax_Syntax.Total uu____21375) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21393),FStar_Syntax_Syntax.Total
                    (t2,uu____21395)) ->
                     let uu____21412 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21412 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21416),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21418)) ->
                     let uu____21435 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21435 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21439),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21441)) ->
                     let uu____21458 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21458 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21461,FStar_Syntax_Syntax.Comp uu____21462) ->
                     let uu____21471 =
                       let uu___160_21476 = problem  in
                       let uu____21481 =
                         let uu____21482 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21482
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___160_21476.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21481;
                         FStar_TypeChecker_Common.relation =
                           (uu___160_21476.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___160_21476.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___160_21476.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___160_21476.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___160_21476.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___160_21476.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___160_21476.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___160_21476.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21471 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21483,FStar_Syntax_Syntax.Comp uu____21484) ->
                     let uu____21493 =
                       let uu___160_21498 = problem  in
                       let uu____21503 =
                         let uu____21504 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21504
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___160_21498.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21503;
                         FStar_TypeChecker_Common.relation =
                           (uu___160_21498.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___160_21498.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___160_21498.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___160_21498.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___160_21498.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___160_21498.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___160_21498.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___160_21498.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21493 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21505,FStar_Syntax_Syntax.GTotal uu____21506) ->
                     let uu____21515 =
                       let uu___161_21520 = problem  in
                       let uu____21525 =
                         let uu____21526 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21526
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___161_21520.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___161_21520.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___161_21520.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21525;
                         FStar_TypeChecker_Common.element =
                           (uu___161_21520.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___161_21520.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___161_21520.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___161_21520.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___161_21520.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___161_21520.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21515 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21527,FStar_Syntax_Syntax.Total uu____21528) ->
                     let uu____21537 =
                       let uu___161_21542 = problem  in
                       let uu____21547 =
                         let uu____21548 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21548
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___161_21542.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___161_21542.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___161_21542.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21547;
                         FStar_TypeChecker_Common.element =
                           (uu___161_21542.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___161_21542.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___161_21542.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___161_21542.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___161_21542.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___161_21542.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21537 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21549,FStar_Syntax_Syntax.Comp uu____21550) ->
                     let uu____21551 =
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
                     if uu____21551
                     then
                       let uu____21552 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____21552 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21558 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21568 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____21569 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____21568, uu____21569))
                             in
                          match uu____21558 with
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
                           (let uu____21576 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____21576
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21578 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____21578 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21581 =
                                  let uu____21582 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____21583 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____21582 uu____21583
                                   in
                                giveup env uu____21581 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____21588 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21626  ->
              match uu____21626 with
              | (uu____21639,uu____21640,u,uu____21642,uu____21643,uu____21644)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____21588 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____21675 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____21675 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____21693 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21721  ->
                match uu____21721 with
                | (u1,u2) ->
                    let uu____21728 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____21729 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____21728 uu____21729))
         in
      FStar_All.pipe_right uu____21693 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21746,[])) -> "{}"
      | uu____21771 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21788 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____21788
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____21791 =
              FStar_List.map
                (fun uu____21801  ->
                   match uu____21801 with
                   | (uu____21806,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____21791 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____21811 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21811 imps
  
let new_t_problem :
  'Auu____21819 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21819 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21819)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21853 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel")
                   in
                if uu____21853
                then
                  let uu____21854 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs  in
                  let uu____21855 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs  in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21854
                    (rel_to_string rel) uu____21855
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
            let uu____21879 =
              let uu____21882 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____21882
               in
            FStar_Syntax_Syntax.new_bv uu____21879 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____21891 =
              let uu____21894 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____21894
               in
            let uu____21897 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____21891 uu____21897  in
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
          let uu____21927 = FStar_Options.eager_inference ()  in
          if uu____21927
          then
            let uu___162_21928 = probs  in
            {
              attempting = (uu___162_21928.attempting);
              wl_deferred = (uu___162_21928.wl_deferred);
              ctr = (uu___162_21928.ctr);
              defer_ok = false;
              smt_ok = (uu___162_21928.smt_ok);
              tcenv = (uu___162_21928.tcenv)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            ((let uu____21939 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____21939
              then
                let uu____21940 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____21940
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
          ((let uu____21954 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____21954
            then
              let uu____21955 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21955
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____21959 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____21959
             then
               let uu____21960 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21960
             else ());
            (let f2 =
               let uu____21963 =
                 let uu____21964 = FStar_Syntax_Util.unmeta f1  in
                 uu____21964.FStar_Syntax_Syntax.n  in
               match uu____21963 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21968 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___163_21969 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___163_21969.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___163_21969.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___163_21969.FStar_TypeChecker_Env.implicits)
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
            let uu____21988 =
              let uu____21989 =
                let uu____21990 =
                  let uu____21991 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____21991
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21990;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____21989  in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____21988
  
let with_guard_no_simp :
  'Auu____22018 .
    'Auu____22018 ->
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
            let uu____22038 =
              let uu____22039 =
                let uu____22040 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____22040
                  (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____22039;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____22038
  
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
          (let uu____22078 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____22078
           then
             let uu____22079 = FStar_Syntax_Print.term_to_string t1  in
             let uu____22080 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____22079
               uu____22080
           else ());
          (let prob =
             let uu____22083 =
               let uu____22088 = FStar_TypeChecker_Env.get_range env  in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____22088
                in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____22083
              in
           let g =
             let uu____22096 =
               let uu____22099 = singleton' env prob smt_ok  in
               solve_and_commit env uu____22099
                 (fun uu____22101  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob) uu____22096  in
           g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22119 = try_teq true env t1 t2  in
        match uu____22119 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____22123 = FStar_TypeChecker_Env.get_range env  in
              let uu____22124 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____22123 uu____22124);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____22131 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____22131
              then
                let uu____22132 = FStar_Syntax_Print.term_to_string t1  in
                let uu____22133 = FStar_Syntax_Print.term_to_string t2  in
                let uu____22134 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____22132
                  uu____22133 uu____22134
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
          let uu____22148 = FStar_TypeChecker_Env.get_range env  in
          let uu____22149 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____22148 uu____22149
  
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____22166 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22166
         then
           let uu____22167 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____22168 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____22167
             uu____22168
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB  in
         let prob =
           let uu____22173 =
             let uu____22178 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____22178 "sub_comp"
              in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____22173
            in
         let uu____22183 =
           let uu____22186 = singleton env prob  in
           solve_and_commit env uu____22186
             (fun uu____22188  -> FStar_Pervasives_Native.None)
            in
         FStar_All.pipe_left (with_guard env prob) uu____22183)
  
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
      fun uu____22217  ->
        match uu____22217 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22256 =
                 let uu____22261 =
                   let uu____22262 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____22263 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____22262 uu____22263
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____22261)  in
               let uu____22264 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____22256 uu____22264)
               in
            let equiv1 v1 v' =
              let uu____22272 =
                let uu____22277 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____22278 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____22277, uu____22278)  in
              match uu____22272 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22297 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22327 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____22327 with
                      | FStar_Syntax_Syntax.U_unif uu____22334 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22363  ->
                                    match uu____22363 with
                                    | (u,v') ->
                                        let uu____22372 = equiv1 v1 v'  in
                                        if uu____22372
                                        then
                                          let uu____22375 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____22375 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____22391 -> []))
               in
            let uu____22396 =
              let wl =
                let uu___164_22400 = empty_worklist env  in
                {
                  attempting = (uu___164_22400.attempting);
                  wl_deferred = (uu___164_22400.wl_deferred);
                  ctr = (uu___164_22400.ctr);
                  defer_ok = false;
                  smt_ok = (uu___164_22400.smt_ok);
                  tcenv = (uu___164_22400.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22418  ->
                      match uu____22418 with
                      | (lb,v1) ->
                          let uu____22425 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____22425 with
                           | USolved wl1 -> ()
                           | uu____22427 -> fail lb v1)))
               in
            let rec check_ineq uu____22435 =
              match uu____22435 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22444) -> true
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
                      uu____22467,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22469,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22480) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22487,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22495 -> false)
               in
            let uu____22500 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22515  ->
                      match uu____22515 with
                      | (u,v1) ->
                          let uu____22522 = check_ineq (u, v1)  in
                          if uu____22522
                          then true
                          else
                            ((let uu____22525 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____22525
                              then
                                let uu____22526 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____22527 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____22526
                                  uu____22527
                              else ());
                             false)))
               in
            if uu____22500
            then ()
            else
              ((let uu____22531 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____22531
                then
                  ((let uu____22533 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22533);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22543 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22543))
                else ());
               (let uu____22553 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____22553))
  
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
      let fail uu____22601 =
        match uu____22601 with
        | (d,s) ->
            let msg = explain env d s  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
              (p_loc d)
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____22615 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____22615
       then
         let uu____22616 = wl_to_string wl  in
         let uu____22617 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits)
            in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22616 uu____22617
       else ());
      (let g1 =
         let uu____22632 = solve_and_commit env wl fail  in
         match uu____22632 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___165_22645 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___165_22645.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___165_22645.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___165_22645.FStar_TypeChecker_Env.implicits)
             }
         | uu____22650 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___166_22654 = g1  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___166_22654.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___166_22654.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___166_22654.FStar_TypeChecker_Env.implicits)
        }))
  
let (last_proof_ns :
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (maybe_update_proof_ns : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns  in
    let uu____22680 = FStar_ST.op_Bang last_proof_ns  in
    match uu____22680 with
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
            let uu___167_22783 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___167_22783.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___167_22783.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___167_22783.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____22784 =
            let uu____22785 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____22785  in
          if uu____22784
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22793 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____22794 =
                       let uu____22795 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22795
                        in
                     FStar_Errors.diag uu____22793 uu____22794)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____22799 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____22800 =
                        let uu____22801 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22801
                         in
                      FStar_Errors.diag uu____22799 uu____22800)
                   else ();
                   (let uu____22804 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in uu____22804 "discharge_guard'" env
                      vc1);
                   (let uu____22805 = check_trivial vc1  in
                    match uu____22805 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22812 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22813 =
                                let uu____22814 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22814
                                 in
                              FStar_Errors.diag uu____22812 uu____22813)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22819 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22820 =
                                let uu____22821 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22821
                                 in
                              FStar_Errors.diag uu____22819 uu____22820)
                           else ();
                           (let vcs =
                              let uu____22832 = FStar_Options.use_tactics ()
                                 in
                              if uu____22832
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22851  ->
                                     (let uu____22853 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left
                                        FStar_Pervasives.ignore uu____22853);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____22855 =
                                   let uu____22862 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____22862)  in
                                 [uu____22855])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22896  ->
                                    match uu____22896 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal
                                           in
                                        let uu____22907 = check_trivial goal1
                                           in
                                        (match uu____22907 with
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
                                                (let uu____22915 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22916 =
                                                   let uu____22917 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   let uu____22918 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22917 uu____22918
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22915 uu____22916)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22921 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22922 =
                                                   let uu____22923 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22923
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22921 uu____22922)
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
      let uu____22933 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____22933 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22939 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____22939
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____22946 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____22946 with
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
          let uu____22965 = FStar_Syntax_Unionfind.find u  in
          match uu____22965 with
          | FStar_Pervasives_Native.None  -> true
          | uu____22968 -> false  in
        let rec until_fixpoint acc implicits =
          let uu____22986 = acc  in
          match uu____22986 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____23072 = hd1  in
                   (match uu____23072 with
                    | (uu____23085,env,u,tm,k,r) ->
                        let uu____23091 = unresolved u  in
                        if uu____23091
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env tm
                              in
                           let env1 =
                             if forcelax
                             then
                               let uu___168_23121 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___168_23121.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___168_23121.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___168_23121.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___168_23121.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___168_23121.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___168_23121.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___168_23121.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___168_23121.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___168_23121.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___168_23121.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___168_23121.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___168_23121.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___168_23121.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___168_23121.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___168_23121.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___168_23121.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___168_23121.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___168_23121.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___168_23121.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___168_23121.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___168_23121.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___168_23121.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___168_23121.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___168_23121.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___168_23121.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___168_23121.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___168_23121.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___168_23121.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___168_23121.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___168_23121.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___168_23121.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___168_23121.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___168_23121.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___168_23121.FStar_TypeChecker_Env.dep_graph)
                               }
                             else env  in
                           (let uu____23124 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck")
                               in
                            if uu____23124
                            then
                              let uu____23125 =
                                FStar_Syntax_Print.uvar_to_string u  in
                              let uu____23126 =
                                FStar_Syntax_Print.term_to_string tm1  in
                              let uu____23127 =
                                FStar_Syntax_Print.term_to_string k  in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____23125 uu____23126 uu____23127
                            else ());
                           (let g1 =
                              try
                                env1.FStar_TypeChecker_Env.check_type_of
                                  must_total env1 tm1 k
                              with
                              | e ->
                                  ((let uu____23138 =
                                      let uu____23147 =
                                        let uu____23154 =
                                          let uu____23155 =
                                            FStar_Syntax_Print.uvar_to_string
                                              u
                                             in
                                          let uu____23156 =
                                            FStar_TypeChecker_Normalize.term_to_string
                                              env1 tm1
                                             in
                                          FStar_Util.format2
                                            "Failed while checking implicit %s set to %s"
                                            uu____23155 uu____23156
                                           in
                                        (FStar_Errors.Error_BadImplicit,
                                          uu____23154, r)
                                         in
                                      [uu____23147]  in
                                    FStar_Errors.add_errors uu____23138);
                                   FStar_Exn.raise e)
                               in
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___171_23170 = g1  in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___171_23170.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___171_23170.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___171_23170.FStar_TypeChecker_Env.implicits)
                                }
                              else g1  in
                            let g' =
                              let uu____23173 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____23179  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true
                                 in
                              match uu____23173 with
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
        let uu___172_23207 = g  in
        let uu____23208 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___172_23207.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___172_23207.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___172_23207.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____23208
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
        let uu____23262 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____23262 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23275 = discharge_guard env g1  in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____23275
      | (reason,uu____23277,uu____23278,e,t,r)::uu____23282 ->
          let uu____23309 =
            let uu____23314 =
              let uu____23315 = FStar_Syntax_Print.term_to_string t  in
              let uu____23316 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format2
                "Failed to resolve implicit argument of type '%s' introduced in %s"
                uu____23315 uu____23316
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____23314)
             in
          FStar_Errors.raise_error uu____23309 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___173_23323 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___173_23323.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___173_23323.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___173_23323.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____23346 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23346 with
      | FStar_Pervasives_Native.Some uu____23351 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23361 = try_teq false env t1 t2  in
        match uu____23361 with
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
        (let uu____23381 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23381
         then
           let uu____23382 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23383 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23382
             uu____23383
         else ());
        (let uu____23385 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____23385 with
         | (prob,x) ->
             let g =
               let uu____23401 =
                 let uu____23404 = singleton' env prob true  in
                 solve_and_commit env uu____23404
                   (fun uu____23406  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23401  in
             ((let uu____23416 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____23416
               then
                 let uu____23417 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____23418 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____23419 =
                   let uu____23420 = FStar_Util.must g  in
                   guard_to_string env uu____23420  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23417 uu____23418 uu____23419
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
        let uu____23448 = check_subtyping env t1 t2  in
        match uu____23448 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23467 =
              let uu____23468 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____23468 g  in
            FStar_Pervasives_Native.Some uu____23467
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23480 = check_subtyping env t1 t2  in
        match uu____23480 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23499 =
              let uu____23500 =
                let uu____23501 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____23501]  in
              close_guard env uu____23500 g  in
            FStar_Pervasives_Native.Some uu____23499
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23512 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23512
         then
           let uu____23513 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23514 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23513
             uu____23514
         else ());
        (let uu____23516 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____23516 with
         | (prob,x) ->
             let g =
               let uu____23526 =
                 let uu____23529 = singleton' env prob false  in
                 solve_and_commit env uu____23529
                   (fun uu____23531  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23526  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23542 =
                      let uu____23543 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____23543]  in
                    close_guard env uu____23542 g1  in
                  discharge_guard_nosmt env g2))
  