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
    ('Auu____1139,'Auu____1140) FStar_TypeChecker_Common.problem ->
      ('Auu____1139,'Auu____1140) FStar_TypeChecker_Common.problem
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
    ('Auu____1165,'Auu____1166) FStar_TypeChecker_Common.problem ->
      ('Auu____1165,'Auu____1166) FStar_TypeChecker_Common.problem
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
        'Auu____1441 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____1441 ->
              'Auu____1442 FStar_Pervasives_Native.option ->
                Prims.string ->
                  ('Auu____1441,'Auu____1442)
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
      'Auu____1494 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1494 ->
            'Auu____1495 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                Prims.string ->
                  ('Auu____1494,'Auu____1495)
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
      'Auu____1547 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____1547 ->
            'Auu____1548 FStar_Pervasives_Native.option ->
              Prims.string ->
                ('Auu____1547,'Auu____1548) FStar_TypeChecker_Common.problem
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
    'Auu____3375 ->
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
    'Auu____3427 ->
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
            let fvs_t = FStar_Syntax_Free.names t  in
            let uu____3482 = occurs_check env wl uk t  in
            match uu____3482 with
            | (occurs_ok,msg) ->
                let uu____3513 = FStar_Util.set_is_subset_of fvs_t fvs  in
                (occurs_ok, uu____3513, (msg, fvs, fvs_t))
  
let intersect_vars :
  'Auu____3536 'Auu____3537 .
    (FStar_Syntax_Syntax.bv,'Auu____3536) FStar_Pervasives_Native.tuple2
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
    (FStar_Syntax_Syntax.bv,'Auu____3862) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____3863) FStar_Pervasives_Native.tuple2
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
      (FStar_Syntax_Syntax.bv,'Auu____3953) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____3954)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.bv,'Auu____3954)
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
              | (uu____7061,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r  in
                  let uu____7086 = new_uvar r scope1 k  in
                  (match uu____7086 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7104 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r
                          in
                       let uu____7121 =
                         let uu____7122 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm"
                            in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____7122
                          in
                       ((T (gi_xs, mk_kind)), uu____7121))
              | (uu____7135,uu____7136,C uu____7137) -> failwith "impos"  in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7284 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7301;
                         FStar_Syntax_Syntax.vars = uu____7302;_})
                        ->
                        let uu____7325 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____7325 with
                         | (T (gi_xs,uu____7349),prob) ->
                             let uu____7359 =
                               let uu____7360 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____7360
                                in
                             (uu____7359, [prob])
                         | uu____7363 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7378;
                         FStar_Syntax_Syntax.vars = uu____7379;_})
                        ->
                        let uu____7402 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____7402 with
                         | (T (gi_xs,uu____7426),prob) ->
                             let uu____7436 =
                               let uu____7437 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                                  in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____7437
                                in
                             (uu____7436, [prob])
                         | uu____7440 -> failwith "impossible")
                    | (uu____7451,uu____7452,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7454;
                         FStar_Syntax_Syntax.vars = uu____7455;_})
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
                        let uu____7586 =
                          let uu____7595 =
                            FStar_List.map (sub_prob scope1 args) components1
                             in
                          FStar_All.pipe_right uu____7595 FStar_List.unzip
                           in
                        (match uu____7586 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7649 =
                                 let uu____7650 =
                                   let uu____7653 = FStar_List.hd tcs  in
                                   FStar_All.pipe_right uu____7653 un_T  in
                                 let uu____7654 =
                                   let uu____7663 = FStar_List.tl tcs  in
                                   FStar_All.pipe_right uu____7663
                                     (FStar_List.map arg_of_tc)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7650;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7654;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 }  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7649
                                in
                             ((C gi_xs), sub_probs))
                    | uu____7672 ->
                        let uu____7685 = sub_prob scope1 args q  in
                        (match uu____7685 with
                         | (ktec,prob) -> (ktec, [prob]))
                     in
                  (match uu____7284 with
                   | (tc,probs) ->
                       let uu____7716 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7779,uu____7780),T
                            (t,uu____7782)) ->
                             let b1 =
                               ((let uu___126_7819 = b  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___126_7819.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___126_7819.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp)
                                in
                             let uu____7820 =
                               let uu____7827 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1
                                  in
                               uu____7827 :: args  in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7820)
                         | uu____7862 ->
                             (FStar_Pervasives_Native.None, scope1, args)
                          in
                       (match uu____7716 with
                        | (bopt,scope2,args1) ->
                            let uu____7946 = aux scope2 args1 qs2  in
                            (match uu____7946 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____7983 =
                                         let uu____7986 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst))
                                            in
                                         f :: uu____7986  in
                                       FStar_Syntax_Util.mk_conj_l uu____7983
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____8009 =
                                         let uu____8012 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f
                                            in
                                         let uu____8013 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst))
                                            in
                                         uu____8012 :: uu____8013  in
                                       FStar_Syntax_Util.mk_conj_l uu____8009
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
  'Auu____8081 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8081)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8081)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___127_8102 = p  in
      let uu____8107 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8108 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___127_8102.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8107;
        FStar_TypeChecker_Common.relation =
          (uu___127_8102.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8108;
        FStar_TypeChecker_Common.element =
          (uu___127_8102.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___127_8102.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___127_8102.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___127_8102.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___127_8102.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___127_8102.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8120 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____8120
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____8129 -> p
  
let (rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8149 = compress_prob wl pr  in
        FStar_All.pipe_right uu____8149 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8159 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8159 with
           | (lh,uu____8179) ->
               let uu____8200 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8200 with
                | (rh,uu____8220) ->
                    let uu____8241 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8258,FStar_Syntax_Syntax.Tm_uvar uu____8259)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8296,uu____8297)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8318,FStar_Syntax_Syntax.Tm_uvar uu____8319)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8340,uu____8341)
                          ->
                          let uu____8358 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____8358 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8407 ->
                                    let rank =
                                      let uu____8415 = is_top_level_prob prob
                                         in
                                      if uu____8415
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____8417 =
                                      let uu___128_8422 = tp  in
                                      let uu____8427 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___128_8422.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___128_8422.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___128_8422.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8427;
                                        FStar_TypeChecker_Common.element =
                                          (uu___128_8422.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___128_8422.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___128_8422.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___128_8422.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___128_8422.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___128_8422.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____8417)))
                      | (uu____8438,FStar_Syntax_Syntax.Tm_uvar uu____8439)
                          ->
                          let uu____8456 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____8456 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8505 ->
                                    let uu____8512 =
                                      let uu___129_8519 = tp  in
                                      let uu____8524 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___129_8519.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8524;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___129_8519.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___129_8519.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___129_8519.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___129_8519.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___129_8519.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___129_8519.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___129_8519.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___129_8519.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____8512)))
                      | (uu____8541,uu____8542) -> (rigid_rigid, tp)  in
                    (match uu____8241 with
                     | (rank,tp1) ->
                         let uu____8561 =
                           FStar_All.pipe_right
                             (let uu___130_8567 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___130_8567.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___130_8567.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___130_8567.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___130_8567.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___130_8567.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___130_8567.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___130_8567.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___130_8567.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___130_8567.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50)
                            in
                         (rank, uu____8561))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8577 =
            FStar_All.pipe_right
              (let uu___131_8583 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___131_8583.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___131_8583.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___131_8583.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___131_8583.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___131_8583.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___131_8583.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___131_8583.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___131_8583.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___131_8583.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51)
             in
          (rigid_rigid, uu____8577)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun wl  ->
    let rec aux uu____8638 probs =
      match uu____8638 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8691 = rank wl hd1  in
               (match uu____8691 with
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
    match projectee with | UDeferred _0 -> true | uu____8798 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8810 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8822 -> false
  
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
                        let uu____8862 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8862 with
                        | (k,uu____8868) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8878 -> false)))
            | uu____8879 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8927 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8933 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8933 = (Prims.parse_int "0")))
                           in
                        if uu____8927 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8947 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8953 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8953 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8947)
               in
            let uu____8954 = filter1 u12  in
            let uu____8957 = filter1 u22  in (uu____8954, uu____8957)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8980 = filter_out_common_univs us1 us2  in
                (match uu____8980 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____9033 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____9033 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____9036 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____9046 =
                          let uu____9047 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____9048 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____9047
                            uu____9048
                           in
                        UFailed uu____9046))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9068 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9068 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9090 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9090 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____9093 ->
                let uu____9098 =
                  let uu____9099 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____9100 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____9099
                    uu____9100 msg
                   in
                UFailed uu____9098
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9101,uu____9102) ->
              let uu____9103 =
                let uu____9104 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9105 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9104 uu____9105
                 in
              failwith uu____9103
          | (FStar_Syntax_Syntax.U_unknown ,uu____9106) ->
              let uu____9107 =
                let uu____9108 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9109 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9108 uu____9109
                 in
              failwith uu____9107
          | (uu____9110,FStar_Syntax_Syntax.U_bvar uu____9111) ->
              let uu____9112 =
                let uu____9113 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9114 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9113 uu____9114
                 in
              failwith uu____9112
          | (uu____9115,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9116 =
                let uu____9117 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9118 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9117 uu____9118
                 in
              failwith uu____9116
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9142 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____9142
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____9164 = occurs_univ v1 u3  in
              if uu____9164
              then
                let uu____9165 =
                  let uu____9166 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9167 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9166 uu____9167
                   in
                try_umax_components u11 u21 uu____9165
              else
                (let uu____9169 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9169)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____9189 = occurs_univ v1 u3  in
              if uu____9189
              then
                let uu____9190 =
                  let uu____9191 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9192 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9191 uu____9192
                   in
                try_umax_components u11 u21 uu____9190
              else
                (let uu____9194 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9194)
          | (FStar_Syntax_Syntax.U_max uu____9203,uu____9204) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9210 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9210
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9212,FStar_Syntax_Syntax.U_max uu____9213) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9219 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9219
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9221,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9222,FStar_Syntax_Syntax.U_name
             uu____9223) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9224) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9225) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9226,FStar_Syntax_Syntax.U_succ
             uu____9227) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9228,FStar_Syntax_Syntax.U_zero
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
      let uu____9314 = bc1  in
      match uu____9314 with
      | (bs1,mk_cod1) ->
          let uu____9355 = bc2  in
          (match uu____9355 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____9425 = FStar_Util.first_N n1 bs  in
                 match uu____9425 with
                 | (bs3,rest) ->
                     let uu____9450 = mk_cod rest  in (bs3, uu____9450)
                  in
               let l1 = FStar_List.length bs1  in
               let l2 = FStar_List.length bs2  in
               if l1 = l2
               then
                 let uu____9479 =
                   let uu____9486 = mk_cod1 []  in (bs1, uu____9486)  in
                 let uu____9489 =
                   let uu____9496 = mk_cod2 []  in (bs2, uu____9496)  in
                 (uu____9479, uu____9489)
               else
                 if l1 > l2
                 then
                   (let uu____9538 = curry l2 bs1 mk_cod1  in
                    let uu____9551 =
                      let uu____9558 = mk_cod2 []  in (bs2, uu____9558)  in
                    (uu____9538, uu____9551))
                 else
                   (let uu____9574 =
                      let uu____9581 = mk_cod1 []  in (bs1, uu____9581)  in
                    let uu____9584 = curry l1 bs2 mk_cod2  in
                    (uu____9574, uu____9584)))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____9705 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____9705
       then
         let uu____9706 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9706
       else ());
      (let uu____9708 = next_prob probs  in
       match uu____9708 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___132_9729 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___132_9729.wl_deferred);
               ctr = (uu___132_9729.ctr);
               defer_ok = (uu___132_9729.defer_ok);
               smt_ok = (uu___132_9729.smt_ok);
               tcenv = (uu___132_9729.tcenv)
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
                  let uu____9740 = solve_flex_rigid_join env tp probs1  in
                  (match uu____9740 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9745 = solve_rigid_flex_meet env tp probs1  in
                     match uu____9745 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9750,uu____9751) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9768 ->
                let uu____9777 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9836  ->
                          match uu____9836 with
                          | (c,uu____9844,uu____9845) -> c < probs.ctr))
                   in
                (match uu____9777 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9886 =
                            FStar_List.map
                              (fun uu____9901  ->
                                 match uu____9901 with
                                 | (uu____9912,x,y) -> (x, y))
                              probs.wl_deferred
                             in
                          Success uu____9886
                      | uu____9915 ->
                          let uu____9924 =
                            let uu___133_9925 = probs  in
                            let uu____9926 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9947  ->
                                      match uu____9947 with
                                      | (uu____9954,uu____9955,y) -> y))
                               in
                            {
                              attempting = uu____9926;
                              wl_deferred = rest;
                              ctr = (uu___133_9925.ctr);
                              defer_ok = (uu___133_9925.defer_ok);
                              smt_ok = (uu___133_9925.smt_ok);
                              tcenv = (uu___133_9925.tcenv)
                            }  in
                          solve env uu____9924))))

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
            let uu____9962 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____9962 with
            | USolved wl1 ->
                let uu____9964 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____9964
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
                  let uu____10010 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10010 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10013 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10025;
                  FStar_Syntax_Syntax.vars = uu____10026;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10029;
                  FStar_Syntax_Syntax.vars = uu____10030;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10044,uu____10045) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10052,FStar_Syntax_Syntax.Tm_uinst uu____10053) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10060 -> USolved wl

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
            ((let uu____10070 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10070
              then
                let uu____10071 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10071 msg
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
        (let uu____10080 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____10080
         then
           let uu____10081 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____10081
         else ());
        (let uu____10083 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____10083 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____10145 = head_matches_delta env () t1 t2  in
               match uu____10145 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____10186 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____10235 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10250 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____10251 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____10250, uu____10251)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10256 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____10257 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____10256, uu____10257)
                           in
                        (match uu____10235 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____10283 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____10283
                                in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____10314 =
                                    let uu____10323 =
                                      let uu____10326 =
                                        let uu____10329 =
                                          let uu____10330 =
                                            let uu____10337 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2
                                               in
                                            (x, uu____10337)  in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____10330
                                           in
                                        FStar_Syntax_Syntax.mk uu____10329
                                         in
                                      uu____10326
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____10345 =
                                      let uu____10348 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort
                                         in
                                      [uu____10348]  in
                                    (uu____10323, uu____10345)  in
                                  FStar_Pervasives_Native.Some uu____10314
                              | (uu____10361,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10363)) ->
                                  let uu____10368 =
                                    let uu____10375 =
                                      let uu____10378 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11
                                         in
                                      [uu____10378]  in
                                    (t11, uu____10375)  in
                                  FStar_Pervasives_Native.Some uu____10368
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10388),uu____10389) ->
                                  let uu____10394 =
                                    let uu____10401 =
                                      let uu____10404 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21
                                         in
                                      [uu____10404]  in
                                    (t21, uu____10401)  in
                                  FStar_Pervasives_Native.Some uu____10394
                              | uu____10413 ->
                                  let uu____10418 =
                                    FStar_Syntax_Util.head_and_args t11  in
                                  (match uu____10418 with
                                   | (head1,uu____10442) ->
                                       let uu____10463 =
                                         let uu____10464 =
                                           FStar_Syntax_Util.un_uinst head1
                                            in
                                         uu____10464.FStar_Syntax_Syntax.n
                                          in
                                       (match uu____10463 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10475;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10477;_}
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
                                        | uu____10484 ->
                                            FStar_Pervasives_Native.None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10497) ->
                  let uu____10522 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___105_10548  ->
                            match uu___105_10548 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10555 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____10555 with
                                      | (u',uu____10571) ->
                                          let uu____10592 =
                                            let uu____10593 = whnf env u'  in
                                            uu____10593.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____10592 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10597) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10622 -> false))
                                 | uu____10623 -> false)
                            | uu____10626 -> false))
                     in
                  (match uu____10522 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10660 tps =
                         match uu____10660 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10708 =
                                    let uu____10717 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound uu____10717  in
                                  (match uu____10708 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10752 -> FStar_Pervasives_Native.None)
                          in
                       let uu____10761 =
                         let uu____10770 =
                           let uu____10777 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (uu____10777, [])  in
                         make_lower_bound uu____10770 lower_bounds  in
                       (match uu____10761 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10789 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____10789
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
                            ((let uu____10809 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____10809
                              then
                                let wl' =
                                  let uu___134_10811 = wl  in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___134_10811.wl_deferred);
                                    ctr = (uu___134_10811.ctr);
                                    defer_ok = (uu___134_10811.defer_ok);
                                    smt_ok = (uu___134_10811.smt_ok);
                                    tcenv = (uu___134_10811.tcenv)
                                  }  in
                                let uu____10812 = wl_to_string wl'  in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10812
                              else ());
                             (let uu____10814 =
                                solve_t env eq_prob
                                  (let uu___135_10816 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___135_10816.wl_deferred);
                                     ctr = (uu___135_10816.ctr);
                                     defer_ok = (uu___135_10816.defer_ok);
                                     smt_ok = (uu___135_10816.smt_ok);
                                     tcenv = (uu___135_10816.tcenv)
                                   })
                                 in
                              match uu____10814 with
                              | Success uu____10819 ->
                                  let wl1 =
                                    let uu___136_10821 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___136_10821.wl_deferred);
                                      ctr = (uu___136_10821.ctr);
                                      defer_ok = (uu___136_10821.defer_ok);
                                      smt_ok = (uu___136_10821.smt_ok);
                                      tcenv = (uu___136_10821.tcenv)
                                    }  in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1
                                     in
                                  let uu____10823 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds
                                     in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10828 -> FStar_Pervasives_Native.None))))
              | uu____10829 -> failwith "Impossible: Not a rigid-flex"))

and (solve_flex_rigid_join :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10838 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____10838
         then
           let uu____10839 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10839
         else ());
        (let uu____10841 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____10841 with
         | (u,args) ->
             let uu____10880 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____10880 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i  in
                  let base_types_match t1 t2 =
                    let uu____10921 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____10921 with
                    | (h1,args1) ->
                        let uu____10962 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____10962 with
                         | (h2,uu____10982) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____11009 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  if uu____11009
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____11027 =
                                          let uu____11030 =
                                            let uu____11031 =
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
                                                   _0_53) uu____11031
                                             in
                                          [uu____11030]  in
                                        FStar_Pervasives_Native.Some
                                          uu____11027))
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
                                       (let uu____11064 =
                                          let uu____11067 =
                                            let uu____11068 =
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
                                                   _0_54) uu____11068
                                             in
                                          [uu____11067]  in
                                        FStar_Pervasives_Native.Some
                                          uu____11064))
                                  else FStar_Pervasives_Native.None
                              | uu____11082 -> FStar_Pervasives_Native.None))
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
                             let uu____11172 =
                               let uu____11181 =
                                 let uu____11184 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21  in
                                 FStar_Syntax_Util.refine x1 uu____11184  in
                               (uu____11181, m1)  in
                             FStar_Pervasives_Native.Some uu____11172)
                    | (uu____11197,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____11199)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____11247),uu____11248) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____11295 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11348) ->
                       let uu____11373 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___106_11399  ->
                                 match uu___106_11399 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____11406 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____11406 with
                                           | (u',uu____11422) ->
                                               let uu____11443 =
                                                 let uu____11444 =
                                                   whnf env u'  in
                                                 uu____11444.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____11443 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11448) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11473 -> false))
                                      | uu____11474 -> false)
                                 | uu____11477 -> false))
                          in
                       (match uu____11373 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11515 tps =
                              match uu____11515 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11577 =
                                         let uu____11588 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound uu____11588  in
                                       (match uu____11577 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11639 ->
                                       FStar_Pervasives_Native.None)
                               in
                            let uu____11650 =
                              let uu____11661 =
                                let uu____11670 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (uu____11670, [])  in
                              make_upper_bound uu____11661 upper_bounds  in
                            (match uu____11650 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11684 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____11684
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
                                 ((let uu____11710 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____11710
                                   then
                                     let wl' =
                                       let uu___137_11712 = wl  in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___137_11712.wl_deferred);
                                         ctr = (uu___137_11712.ctr);
                                         defer_ok = (uu___137_11712.defer_ok);
                                         smt_ok = (uu___137_11712.smt_ok);
                                         tcenv = (uu___137_11712.tcenv)
                                       }  in
                                     let uu____11713 = wl_to_string wl'  in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11713
                                   else ());
                                  (let uu____11715 =
                                     solve_t env eq_prob
                                       (let uu___138_11717 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___138_11717.wl_deferred);
                                          ctr = (uu___138_11717.ctr);
                                          defer_ok =
                                            (uu___138_11717.defer_ok);
                                          smt_ok = (uu___138_11717.smt_ok);
                                          tcenv = (uu___138_11717.tcenv)
                                        })
                                      in
                                   match uu____11715 with
                                   | Success uu____11720 ->
                                       let wl1 =
                                         let uu___139_11722 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___139_11722.wl_deferred);
                                           ctr = (uu___139_11722.ctr);
                                           defer_ok =
                                             (uu___139_11722.defer_ok);
                                           smt_ok = (uu___139_11722.smt_ok);
                                           tcenv = (uu___139_11722.tcenv)
                                         }  in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1
                                          in
                                       let uu____11724 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds
                                          in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11729 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11730 -> failwith "Impossible: Not a flex-rigid")))

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
                    ((let uu____11805 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____11805
                      then
                        let uu____11806 = prob_to_string env1 rhs_prob  in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11806
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst
                         in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___140_11860 = hd1  in
                      let uu____11861 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___140_11860.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___140_11860.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11861
                      }  in
                    let hd21 =
                      let uu___141_11865 = hd2  in
                      let uu____11866 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___141_11865.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___141_11865.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11866
                      }  in
                    let prob =
                      let uu____11870 =
                        let uu____11875 =
                          FStar_All.pipe_left invert_rel (p_rel orig)  in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11875 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter"
                         in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____11870
                       in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                    let subst2 =
                      let uu____11886 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1
                         in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11886
                       in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                    let uu____11890 =
                      aux (FStar_List.append scope [(hd12, imp)]) env2 subst2
                        xs1 ys1
                       in
                    (match uu____11890 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____11928 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst
                              in
                           let uu____11933 =
                             close_forall env2 [(hd12, imp)] phi  in
                           FStar_Syntax_Util.mk_conj uu____11928 uu____11933
                            in
                         ((let uu____11943 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____11943
                           then
                             let uu____11944 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____11945 =
                               FStar_Syntax_Print.bv_to_string hd12  in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____11944 uu____11945
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____11968 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch"
                 in
              let scope = p_scope orig  in
              let uu____11978 = aux scope env [] bs1 bs2  in
              match uu____11978 with
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
        let uu____12002 = compress_tprob wl problem  in
        solve_t' env uu____12002 wl

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____12035 = head_matches_delta env1 wl1 t1 t2  in
          match uu____12035 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____12066,uu____12067) ->
                   let rec may_relate head3 =
                     let uu____12092 =
                       let uu____12093 = FStar_Syntax_Subst.compress head3
                          in
                       uu____12093.FStar_Syntax_Syntax.n  in
                     match uu____12092 with
                     | FStar_Syntax_Syntax.Tm_name uu____12096 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____12097 -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____12120;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_equational ;
                           FStar_Syntax_Syntax.fv_qual = uu____12121;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____12124;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_abstract uu____12125;
                           FStar_Syntax_Syntax.fv_qual = uu____12126;_}
                         ->
                         problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____12130,uu____12131) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____12173) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____12179) ->
                         may_relate t
                     | uu____12184 -> false  in
                   let uu____12185 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok
                      in
                   if uu____12185
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
                                let uu____12202 =
                                  let uu____12203 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____12203 t21
                                   in
                                FStar_Syntax_Util.mk_forall u_x x uu____12202
                             in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1)
                        in
                     let uu____12205 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1
                        in
                     solve env1 uu____12205
                   else
                     (let uu____12207 =
                        let uu____12208 =
                          FStar_Syntax_Print.term_to_string head1  in
                        let uu____12209 =
                          FStar_Syntax_Print.term_to_string head2  in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____12208 uu____12209
                         in
                      giveup env1 uu____12207 orig)
               | (uu____12210,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___142_12224 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___142_12224.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___142_12224.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___142_12224.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___142_12224.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___142_12224.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___142_12224.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___142_12224.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___142_12224.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____12225,FStar_Pervasives_Native.None ) ->
                   ((let uu____12237 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____12237
                     then
                       let uu____12238 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12239 = FStar_Syntax_Print.tag_of_term t1
                          in
                       let uu____12240 = FStar_Syntax_Print.term_to_string t2
                          in
                       let uu____12241 = FStar_Syntax_Print.tag_of_term t2
                          in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____12238
                         uu____12239 uu____12240 uu____12241
                     else ());
                    (let uu____12243 = FStar_Syntax_Util.head_and_args t1  in
                     match uu____12243 with
                     | (head11,args1) ->
                         let uu____12280 = FStar_Syntax_Util.head_and_args t2
                            in
                         (match uu____12280 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1  in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____12334 =
                                  let uu____12335 =
                                    FStar_Syntax_Print.term_to_string head11
                                     in
                                  let uu____12336 = args_to_string args1  in
                                  let uu____12337 =
                                    FStar_Syntax_Print.term_to_string head21
                                     in
                                  let uu____12338 = args_to_string args2  in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____12335 uu____12336 uu____12337
                                    uu____12338
                                   in
                                giveup env1 uu____12334 orig
                              else
                                (let uu____12340 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____12346 =
                                        FStar_Syntax_Util.eq_args args1 args2
                                         in
                                      uu____12346 = FStar_Syntax_Util.Equal)
                                    in
                                 if uu____12340
                                 then
                                   let uu____12347 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1
                                      in
                                   match uu____12347 with
                                   | USolved wl2 ->
                                       let uu____12349 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2
                                          in
                                       solve env1 uu____12349
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____12353 =
                                      base_and_refinement env1 t1  in
                                    match uu____12353 with
                                    | (base1,refinement1) ->
                                        let uu____12378 =
                                          base_and_refinement env1 t2  in
                                        (match uu____12378 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____12435 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1
                                                     in
                                                  (match uu____12435 with
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
                                                           (fun uu____12457 
                                                              ->
                                                              fun uu____12458
                                                                 ->
                                                                match 
                                                                  (uu____12457,
                                                                    uu____12458)
                                                                with
                                                                | ((a,uu____12476),
                                                                   (a',uu____12478))
                                                                    ->
                                                                    let uu____12487
                                                                    =
                                                                    let uu____12492
                                                                    =
                                                                    p_scope
                                                                    orig  in
                                                                    mk_problem
                                                                    uu____12492
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
                                                                    uu____12487)
                                                           args1 args2
                                                          in
                                                       let formula =
                                                         let uu____12498 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____12498
                                                          in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2
                                                          in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____12504 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1)
                                                     in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2)
                                                     in
                                                  solve_t env1
                                                    (let uu___143_12540 =
                                                       problem  in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___143_12540.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___143_12540.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___143_12540.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___143_12540.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___143_12540.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___143_12540.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___143_12540.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___143_12540.FStar_TypeChecker_Common.rank)
                                                     }) wl1))))))))
           in
        let force_quasi_pattern xs_opt uu____12573 =
          match uu____12573 with
          | (t,u,k,args) ->
              let debug1 f =
                let uu____12615 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12615 then f () else ()  in
              let rec aux pat_args pat_args_set pattern_vars pattern_var_set
                seen_formals formals res_t args1 =
                debug1
                  (fun uu____12711  ->
                     let uu____12712 =
                       FStar_Syntax_Print.binders_to_string ", " pat_args  in
                     FStar_Util.print1 "pat_args so far: {%s}\n" uu____12712);
                (match (formals, args1) with
                 | ([],[]) ->
                     let pat_args1 =
                       FStar_All.pipe_right (FStar_List.rev pat_args)
                         (FStar_List.map
                            (fun uu____12780  ->
                               match uu____12780 with
                               | (x,imp) ->
                                   let uu____12791 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   (uu____12791, imp)))
                        in
                     let pattern_vars1 = FStar_List.rev pattern_vars  in
                     let kk =
                       let uu____12804 = FStar_Syntax_Util.type_u ()  in
                       match uu____12804 with
                       | (t1,uu____12810) ->
                           let uu____12811 =
                             new_uvar t1.FStar_Syntax_Syntax.pos
                               pattern_vars1 t1
                              in
                           FStar_Pervasives_Native.fst uu____12811
                        in
                     let uu____12816 =
                       new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk
                        in
                     (match uu____12816 with
                      | (t',tm_u1) ->
                          let uu____12829 = destruct_flex_t t'  in
                          (match uu____12829 with
                           | (uu____12866,u1,k1,uu____12869) ->
                               let all_formals = FStar_List.rev seen_formals
                                  in
                               let k2 =
                                 let uu____12928 =
                                   FStar_Syntax_Syntax.mk_Total res_t  in
                                 FStar_Syntax_Util.arrow all_formals
                                   uu____12928
                                  in
                               let sol =
                                 let uu____12932 =
                                   let uu____12941 = u_abs k2 all_formals t'
                                      in
                                   ((u, k2), uu____12941)  in
                                 TERM uu____12932  in
                               let t_app =
                                 FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                   pat_args1 FStar_Pervasives_Native.None
                                   t.FStar_Syntax_Syntax.pos
                                  in
                               FStar_Pervasives_Native.Some
                                 (sol, (t_app, u1, k1, pat_args1))))
                 | (formal::formals1,hd1::tl1) ->
                     (debug1
                        (fun uu____13076  ->
                           let uu____13077 =
                             FStar_Syntax_Print.binder_to_string formal  in
                           let uu____13078 =
                             FStar_Syntax_Print.args_to_string [hd1]  in
                           FStar_Util.print2
                             "force_quasi_pattern (case 2): formal=%s, hd=%s\n"
                             uu____13077 uu____13078);
                      (let uu____13091 = pat_var_opt env pat_args hd1  in
                       match uu____13091 with
                       | FStar_Pervasives_Native.None  ->
                           (debug1
                              (fun uu____13111  ->
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
                                      (fun uu____13154  ->
                                         match uu____13154 with
                                         | (x,uu____13160) ->
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
                                (fun uu____13175  ->
                                   let uu____13176 =
                                     FStar_Syntax_Print.args_to_string [hd1]
                                      in
                                   let uu____13189 =
                                     FStar_Syntax_Print.binder_to_string y
                                      in
                                   FStar_Util.print2
                                     "%s (var = %s) maybe pat\n" uu____13176
                                     uu____13189);
                              (let fvs =
                                 FStar_Syntax_Free.names
                                   (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort
                                  in
                               let uu____13193 =
                                 let uu____13194 =
                                   FStar_Util.set_is_subset_of fvs
                                     pat_args_set
                                    in
                                 Prims.op_Negation uu____13194  in
                               if uu____13193
                               then
                                 (debug1
                                    (fun uu____13206  ->
                                       let uu____13207 =
                                         let uu____13210 =
                                           FStar_Syntax_Print.args_to_string
                                             [hd1]
                                            in
                                         let uu____13223 =
                                           let uu____13226 =
                                             FStar_Syntax_Print.binder_to_string
                                               y
                                              in
                                           let uu____13227 =
                                             let uu____13230 =
                                               FStar_Syntax_Print.term_to_string
                                                 (FStar_Pervasives_Native.fst
                                                    y).FStar_Syntax_Syntax.sort
                                                in
                                             let uu____13231 =
                                               let uu____13234 =
                                                 names_to_string fvs  in
                                               let uu____13235 =
                                                 let uu____13238 =
                                                   names_to_string
                                                     pattern_var_set
                                                    in
                                                 [uu____13238]  in
                                               uu____13234 :: uu____13235  in
                                             uu____13230 :: uu____13231  in
                                           uu____13226 :: uu____13227  in
                                         uu____13210 :: uu____13223  in
                                       FStar_Util.print
                                         "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n"
                                         uu____13207);
                                  aux pat_args pat_args_set pattern_vars
                                    pattern_var_set (formal :: seen_formals)
                                    formals1 res_t tl1)
                               else
                                 (let uu____13240 =
                                    FStar_Util.set_add
                                      (FStar_Pervasives_Native.fst y)
                                      pat_args_set
                                     in
                                  let uu____13243 =
                                    FStar_Util.set_add
                                      (FStar_Pervasives_Native.fst formal)
                                      pattern_var_set
                                     in
                                  aux (y :: pat_args) uu____13240 (formal ::
                                    pattern_vars) uu____13243 (formal ::
                                    seen_formals) formals1 res_t tl1)))))
                 | ([],uu____13250::uu____13251) ->
                     let uu____13282 =
                       let uu____13295 =
                         FStar_TypeChecker_Normalize.unfold_whnf env res_t
                          in
                       FStar_Syntax_Util.arrow_formals uu____13295  in
                     (match uu____13282 with
                      | (more_formals,res_t1) ->
                          (match more_formals with
                           | [] -> FStar_Pervasives_Native.None
                           | uu____13334 ->
                               aux pat_args pat_args_set pattern_vars
                                 pattern_var_set seen_formals more_formals
                                 res_t1 args1))
                 | (uu____13341::uu____13342,[]) ->
                     FStar_Pervasives_Native.None)
                 in
              let uu____13365 =
                let uu____13378 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k  in
                FStar_Syntax_Util.arrow_formals uu____13378  in
              (match uu____13365 with
               | (all_formals,res_t) ->
                   (debug1
                      (fun uu____13414  ->
                         let uu____13415 =
                           FStar_Syntax_Print.term_to_string t  in
                         let uu____13416 =
                           FStar_Syntax_Print.binders_to_string ", "
                             all_formals
                            in
                         let uu____13417 =
                           FStar_Syntax_Print.term_to_string res_t  in
                         let uu____13418 =
                           FStar_Syntax_Print.args_to_string args  in
                         FStar_Util.print4
                           "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n"
                           uu____13415 uu____13416 uu____13417 uu____13418);
                    (let uu____13419 = FStar_Syntax_Syntax.new_bv_set ()  in
                     let uu____13422 = FStar_Syntax_Syntax.new_bv_set ()  in
                     aux [] uu____13419 [] uu____13422 [] all_formals res_t
                       args)))
           in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____13456 = lhs  in
          match uu____13456 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____13466 ->
                    let uu____13467 = sn_binders env1 pat_vars1  in
                    u_abs k_uv uu____13467 rhs
                 in
              let wl2 =
                solve_prob orig FStar_Pervasives_Native.None
                  [TERM ((uv, k_uv), sol)] wl1
                 in
              solve env1 wl2
           in
        let imitate orig env1 wl1 p =
          let uu____13490 = p  in
          match uu____13490 with
          | (((u,k),xs,c),ps,(h,uu____13501,qs)) ->
              let xs1 = sn_binders env1 xs  in
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____13583 = imitation_sub_probs orig env1 xs1 ps qs  in
              (match uu____13583 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13606 = h gs_xs  in
                     let uu____13607 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57)
                        in
                     FStar_Syntax_Util.abs xs1 uu____13606 uu____13607  in
                   ((let uu____13613 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____13613
                     then
                       let uu____13614 =
                         let uu____13617 =
                           let uu____13618 =
                             FStar_List.map tc_to_string gs_xs  in
                           FStar_All.pipe_right uu____13618
                             (FStar_String.concat "\n\t>")
                            in
                         let uu____13623 =
                           let uu____13626 =
                             FStar_Syntax_Print.binders_to_string ", " xs1
                              in
                           let uu____13627 =
                             let uu____13630 =
                               FStar_Syntax_Print.comp_to_string c  in
                             let uu____13631 =
                               let uu____13634 =
                                 FStar_Syntax_Print.term_to_string im  in
                               let uu____13635 =
                                 let uu____13638 =
                                   FStar_Syntax_Print.tag_of_term im  in
                                 let uu____13639 =
                                   let uu____13642 =
                                     let uu____13643 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs
                                        in
                                     FStar_All.pipe_right uu____13643
                                       (FStar_String.concat ", ")
                                      in
                                   let uu____13648 =
                                     let uu____13651 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula
                                        in
                                     [uu____13651]  in
                                   uu____13642 :: uu____13648  in
                                 uu____13638 :: uu____13639  in
                               uu____13634 :: uu____13635  in
                             uu____13630 :: uu____13631  in
                           uu____13626 :: uu____13627  in
                         uu____13617 :: uu____13623  in
                       FStar_Util.print
                         "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13614
                     else ());
                    def_check_closed (p_loc orig) "imitate" im;
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1
                        in
                     solve env1 (attempt sub_probs wl2))))
           in
        let imitate' orig env1 wl1 uu___107_13673 =
          match uu___107_13673 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p  in
        let project orig env1 wl1 i p =
          let uu____13705 = p  in
          match uu____13705 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____13796 = FStar_List.nth ps i  in
              (match uu____13796 with
               | (pi,uu____13800) ->
                   let uu____13805 = FStar_List.nth xs i  in
                   (match uu____13805 with
                    | (xi,uu____13817) ->
                        let rec gs k =
                          let uu____13830 =
                            let uu____13843 =
                              FStar_TypeChecker_Normalize.unfold_whnf env1 k
                               in
                            FStar_Syntax_Util.arrow_formals uu____13843  in
                          match uu____13830 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____13918)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort
                                       in
                                    let uu____13931 = new_uvar r xs k_a  in
                                    (match uu____13931 with
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
                                         let uu____13953 = aux subst2 tl1  in
                                         (match uu____13953 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____13980 =
                                                let uu____13983 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1
                                                   in
                                                uu____13983 :: gi_xs'  in
                                              let uu____13984 =
                                                let uu____13987 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps
                                                   in
                                                uu____13987 :: gi_ps'  in
                                              (uu____13980, uu____13984)))
                                 in
                              aux [] bs
                           in
                        let uu____13992 =
                          let uu____13993 = matches pi  in
                          FStar_All.pipe_left Prims.op_Negation uu____13993
                           in
                        if uu____13992
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____13997 = gs xi.FStar_Syntax_Syntax.sort
                              in
                           match uu____13997 with
                           | (g_xs,uu____14009) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                  in
                               let proj =
                                 let uu____14020 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r
                                    in
                                 let uu____14021 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_58  ->
                                        FStar_Pervasives_Native.Some _0_58)
                                    in
                                 FStar_Syntax_Util.abs xs uu____14020
                                   uu____14021
                                  in
                               let sub1 =
                                 let uu____14027 =
                                   let uu____14032 = p_scope orig  in
                                   let uu____14033 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r
                                      in
                                   let uu____14036 =
                                     let uu____14039 =
                                       FStar_List.map
                                         (fun uu____14054  ->
                                            match uu____14054 with
                                            | (uu____14063,uu____14064,y) ->
                                                y) qs
                                        in
                                     FStar_All.pipe_left h uu____14039  in
                                   mk_problem uu____14032 orig uu____14033
                                     (p_rel orig) uu____14036
                                     FStar_Pervasives_Native.None
                                     "projection"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____14027
                                  in
                               ((let uu____14079 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____14079
                                 then
                                   let uu____14080 =
                                     FStar_Syntax_Print.term_to_string proj
                                      in
                                   let uu____14081 = prob_to_string env1 sub1
                                      in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____14080 uu____14081
                                 else ());
                                (let wl2 =
                                   let uu____14084 =
                                     let uu____14087 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1)
                                        in
                                     FStar_Pervasives_Native.Some uu____14087
                                      in
                                   solve_prob orig uu____14084
                                     [TERM (u, proj)] wl1
                                    in
                                 let uu____14096 =
                                   solve env1 (attempt [sub1] wl2)  in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____14096)))))
           in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____14127 = lhs  in
          match uu____14127 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____14163 = FStar_Syntax_Util.arrow_formals_comp k_uv
                   in
                match uu____14163 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____14196 =
                        let uu____14243 = decompose env t2  in
                        (((uv, k_uv), xs, c), ps, uu____14243)  in
                      FStar_Pervasives_Native.Some uu____14196
                    else
                      (let rec elim k args =
                         let k1 =
                           FStar_TypeChecker_Normalize.unfold_whnf env k  in
                         let uu____14387 =
                           let uu____14394 =
                             let uu____14395 = FStar_Syntax_Subst.compress k1
                                in
                             uu____14395.FStar_Syntax_Syntax.n  in
                           (uu____14394, args)  in
                         match uu____14387 with
                         | (uu____14406,[]) ->
                             let uu____14409 =
                               let uu____14420 =
                                 FStar_Syntax_Syntax.mk_Total k1  in
                               ([], uu____14420)  in
                             FStar_Pervasives_Native.Some uu____14409
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____14441,uu____14442) ->
                             let uu____14463 =
                               FStar_Syntax_Util.head_and_args k1  in
                             (match uu____14463 with
                              | (uv1,uv_args) ->
                                  let uu____14506 =
                                    let uu____14507 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____14507.FStar_Syntax_Syntax.n  in
                                  (match uu____14506 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14517) ->
                                       let uu____14542 =
                                         pat_vars env [] uv_args  in
                                       (match uu____14542 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14569  ->
                                                      let uu____14570 =
                                                        let uu____14571 =
                                                          let uu____14572 =
                                                            let uu____14577 =
                                                              let uu____14578
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____14578
                                                                FStar_Pervasives_Native.fst
                                                               in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14577
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14572
                                                           in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14571
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14570))
                                               in
                                            let c1 =
                                              let uu____14588 =
                                                let uu____14589 =
                                                  let uu____14594 =
                                                    let uu____14595 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____14595
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14594
                                                   in
                                                FStar_Pervasives_Native.fst
                                                  uu____14589
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14588
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____14608 =
                                                let uu____14611 =
                                                  let uu____14612 =
                                                    let uu____14615 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____14615
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14612
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____14611
                                                 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14608
                                               in
                                            (def_check_closed (p_loc orig)
                                               "solve_t_flex_rigid.subterms"
                                               uv_sol;
                                             FStar_Syntax_Util.set_uvar uvar
                                               uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14634 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14639,uu____14640) ->
                             let uu____14659 =
                               FStar_Syntax_Util.head_and_args k1  in
                             (match uu____14659 with
                              | (uv1,uv_args) ->
                                  let uu____14702 =
                                    let uu____14703 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____14703.FStar_Syntax_Syntax.n  in
                                  (match uu____14702 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14713) ->
                                       let uu____14738 =
                                         pat_vars env [] uv_args  in
                                       (match uu____14738 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14765  ->
                                                      let uu____14766 =
                                                        let uu____14767 =
                                                          let uu____14768 =
                                                            let uu____14773 =
                                                              let uu____14774
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____14774
                                                                FStar_Pervasives_Native.fst
                                                               in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14773
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14768
                                                           in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14767
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14766))
                                               in
                                            let c1 =
                                              let uu____14784 =
                                                let uu____14785 =
                                                  let uu____14790 =
                                                    let uu____14791 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____14791
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14790
                                                   in
                                                FStar_Pervasives_Native.fst
                                                  uu____14785
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14784
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____14804 =
                                                let uu____14807 =
                                                  let uu____14808 =
                                                    let uu____14811 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____14811
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14808
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____14807
                                                 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14804
                                               in
                                            (def_check_closed (p_loc orig)
                                               "solve_t_flex_rigid.subterms"
                                               uv_sol;
                                             FStar_Syntax_Util.set_uvar uvar
                                               uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14830 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____14837) ->
                             let n_args = FStar_List.length args  in
                             let n_xs = FStar_List.length xs1  in
                             if n_xs = n_args
                             then
                               let uu____14878 =
                                 FStar_Syntax_Subst.open_comp xs1 c1  in
                               FStar_All.pipe_right uu____14878
                                 (fun _0_61  ->
                                    FStar_Pervasives_Native.Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____14914 =
                                    FStar_Util.first_N n_xs args  in
                                  match uu____14914 with
                                  | (args1,rest) ->
                                      let uu____14943 =
                                        FStar_Syntax_Subst.open_comp xs1 c1
                                         in
                                      (match uu____14943 with
                                       | (xs2,c2) ->
                                           let uu____14956 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest
                                              in
                                           FStar_Util.bind_opt uu____14956
                                             (fun uu____14980  ->
                                                match uu____14980 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____15020 =
                                    FStar_Util.first_N n_args xs1  in
                                  match uu____15020 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k1.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____15088 =
                                        let uu____15093 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____15093
                                         in
                                      FStar_All.pipe_right uu____15088
                                        (fun _0_62  ->
                                           FStar_Pervasives_Native.Some _0_62))
                         | uu____15108 ->
                             let uu____15115 =
                               let uu____15120 =
                                 let uu____15121 =
                                   FStar_Syntax_Print.uvar_to_string uv  in
                                 let uu____15122 =
                                   FStar_Syntax_Print.term_to_string k1  in
                                 let uu____15123 =
                                   FStar_Syntax_Print.term_to_string k_uv  in
                                 FStar_Util.format3
                                   "Impossible: ill-typed application %s : %s\n\t%s"
                                   uu____15121 uu____15122 uu____15123
                                  in
                               (FStar_Errors.Fatal_IllTyped, uu____15120)  in
                             FStar_Errors.raise_error uu____15115
                               t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15130 = elim k_uv ps  in
                       FStar_Util.bind_opt uu____15130
                         (fun uu____15185  ->
                            match uu____15185 with
                            | (xs1,c1) ->
                                let uu____15234 =
                                  let uu____15275 = decompose env t2  in
                                  (((uv, k_uv), xs1, c1), ps, uu____15275)
                                   in
                                FStar_Pervasives_Native.Some uu____15234))
                 in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail uu____15396 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig
                   in
                let rec try_project st i =
                  if i >= n1
                  then fail ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                     let uu____15410 = project orig env wl1 i st  in
                     match uu____15410 with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some (Failed uu____15424) ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some sol -> sol)
                   in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt  in
                  let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                  let uu____15439 = imitate orig env wl1 st  in
                  match uu____15439 with
                  | Failed uu____15444 ->
                      (FStar_Syntax_Unionfind.rollback tx;
                       try_project st (Prims.parse_int "0"))
                  | sol -> sol
                else fail ()  in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____15475 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1  in
                match uu____15475 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let uu____15498 = forced_lhs_pattern  in
                    (match uu____15498 with
                     | (lhs_t,uu____15500,uu____15501,uu____15502) ->
                         ((let uu____15504 =
                             FStar_TypeChecker_Env.debug env
                               (FStar_Options.Other "Rel")
                              in
                           if uu____15504
                           then
                             let uu____15505 = lhs1  in
                             match uu____15505 with
                             | (t0,uu____15507,uu____15508,uu____15509) ->
                                 let uu____15510 = forced_lhs_pattern  in
                                 (match uu____15510 with
                                  | (t11,uu____15512,uu____15513,uu____15514)
                                      ->
                                      let uu____15515 =
                                        FStar_Syntax_Print.term_to_string t0
                                         in
                                      let uu____15516 =
                                        FStar_Syntax_Print.term_to_string t11
                                         in
                                      FStar_Util.print2
                                        "force_quasi_pattern succeeded, turning %s into %s\n"
                                        uu____15515 uu____15516)
                           else ());
                          (let rhs_vars = FStar_Syntax_Free.names rhs  in
                           let lhs_vars = FStar_Syntax_Free.names lhs_t  in
                           let uu____15524 =
                             FStar_Util.set_is_subset_of rhs_vars lhs_vars
                              in
                           if uu____15524
                           then
                             ((let uu____15526 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "Rel")
                                  in
                               if uu____15526
                               then
                                 let uu____15527 =
                                   FStar_Syntax_Print.term_to_string rhs  in
                                 let uu____15528 = names_to_string rhs_vars
                                    in
                                 let uu____15529 = names_to_string lhs_vars
                                    in
                                 FStar_Util.print3
                                   "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n"
                                   uu____15527 uu____15528 uu____15529
                               else ());
                              (let tx =
                                 FStar_Syntax_Unionfind.new_transaction ()
                                  in
                               let wl2 =
                                 extend_solution (p_pid orig) [sol] wl1  in
                               let uu____15533 =
                                 let uu____15534 =
                                   FStar_TypeChecker_Common.as_tprob orig  in
                                 solve_t env uu____15534 wl2  in
                               match uu____15533 with
                               | Failed uu____15535 ->
                                   (FStar_Syntax_Unionfind.rollback tx;
                                    imitate_or_project n1 lhs1 rhs stopt)
                               | sol1 -> sol1))
                           else
                             ((let uu____15544 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "Rel")
                                  in
                               if uu____15544
                               then
                                 FStar_Util.print_string
                                   "fvar check failed for quasi pattern ... im/proj\n"
                               else ());
                              imitate_or_project n1 lhs1 rhs stopt))))
                 in
              let check_head fvs1 t21 =
                let uu____15557 = FStar_Syntax_Util.head_and_args t21  in
                match uu____15557 with
                | (hd1,uu____15573) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15594 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15607 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15608 -> true
                     | uu____15625 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1  in
                         let uu____15629 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1  in
                         if uu____15629
                         then true
                         else
                           ((let uu____15632 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____15632
                             then
                               let uu____15633 = names_to_string fvs_hd  in
                               FStar_Util.print1 "Free variables are %s\n"
                                 uu____15633
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
                   let uu____15653 = occurs_check env wl1 (uv, k_uv) t21  in
                   (match uu____15653 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15666 =
                            let uu____15667 = FStar_Option.get msg  in
                            Prims.strcat "occurs-check failed: " uu____15667
                             in
                          giveup_or_defer1 orig uu____15666
                        else
                          (let uu____15669 =
                             FStar_Util.set_is_subset_of fvs2 fvs1  in
                           if uu____15669
                           then
                             let uu____15670 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
                                in
                             (if uu____15670
                              then
                                let uu____15671 = subterms args_lhs  in
                                imitate' orig env wl1 uu____15671
                              else
                                ((let uu____15676 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____15676
                                  then
                                    let uu____15677 =
                                      FStar_Syntax_Print.term_to_string t11
                                       in
                                    let uu____15678 = names_to_string fvs1
                                       in
                                    let uu____15679 = names_to_string fvs2
                                       in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15677 uu____15678 uu____15679
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
                               (let uu____15683 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21)
                                   in
                                if uu____15683
                                then
                                  ((let uu____15685 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____15685
                                    then
                                      let uu____15686 =
                                        FStar_Syntax_Print.term_to_string t11
                                         in
                                      let uu____15687 = names_to_string fvs1
                                         in
                                      let uu____15688 = names_to_string fvs2
                                         in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                        uu____15686 uu____15687 uu____15688
                                    else ());
                                   (let uu____15690 = subterms args_lhs  in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) lhs1 t21
                                      uu____15690))
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
                     (let uu____15701 =
                        let uu____15702 = FStar_Syntax_Free.names t1  in
                        check_head uu____15702 t2  in
                      if uu____15701
                      then
                        let n_args_lhs = FStar_List.length args_lhs  in
                        ((let uu____15713 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel")
                             in
                          if uu____15713
                          then
                            let uu____15714 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____15715 =
                              FStar_Util.string_of_int n_args_lhs  in
                            FStar_Util.print2
                              "Not a pattern (%s) ... (lhs has %s args)\n"
                              uu____15714 uu____15715
                          else ());
                         (let uu____15723 = subterms args_lhs  in
                          pattern_eq_imitate_or_project n_args_lhs
                            (FStar_Pervasives_Native.fst lhs) t2 uu____15723))
                      else giveup env "head-symbol is free" orig))
           in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let solve_both_pats wl1 uu____15800 uu____15801 r =
               match (uu____15800, uu____15801) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____15999 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys)
                      in
                   if uu____15999
                   then
                     let uu____16000 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1
                        in
                     solve env uu____16000
                   else
                     (let xs1 = sn_binders env xs  in
                      let ys1 = sn_binders env ys  in
                      let zs = intersect_vars xs1 ys1  in
                      (let uu____16024 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____16024
                       then
                         let uu____16025 =
                           FStar_Syntax_Print.binders_to_string ", " xs1  in
                         let uu____16026 =
                           FStar_Syntax_Print.binders_to_string ", " ys1  in
                         let uu____16027 =
                           FStar_Syntax_Print.binders_to_string ", " zs  in
                         let uu____16028 =
                           FStar_Syntax_Print.term_to_string k1  in
                         let uu____16029 =
                           FStar_Syntax_Print.term_to_string k2  in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____16025 uu____16026 uu____16027 uu____16028
                           uu____16029
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2  in
                         let args_len = FStar_List.length args  in
                         if xs_len = args_len
                         then
                           let uu____16089 =
                             FStar_Syntax_Util.subst_of_list xs2 args  in
                           FStar_Syntax_Subst.subst uu____16089 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____16103 =
                                FStar_Util.first_N args_len xs2  in
                              match uu____16103 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____16157 =
                                      FStar_Syntax_Syntax.mk_GTotal k  in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____16157
                                     in
                                  let uu____16160 =
                                    FStar_Syntax_Util.subst_of_list xs3 args
                                     in
                                  FStar_Syntax_Subst.subst uu____16160 k3)
                           else
                             (let uu____16164 =
                                let uu____16165 =
                                  FStar_Syntax_Print.term_to_string k  in
                                let uu____16166 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2
                                   in
                                let uu____16167 =
                                  FStar_Syntax_Print.args_to_string args  in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____16165 uu____16166 uu____16167
                                 in
                              failwith uu____16164)
                          in
                       let uu____16168 =
                         let uu____16175 =
                           let uu____16188 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1
                              in
                           FStar_Syntax_Util.arrow_formals uu____16188  in
                         match uu____16175 with
                         | (bs,k1') ->
                             let uu____16213 =
                               let uu____16226 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2
                                  in
                               FStar_Syntax_Util.arrow_formals uu____16226
                                in
                             (match uu____16213 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1  in
                                  let k2'_ys = subst_k k2' cs args2  in
                                  let sub_prob =
                                    let uu____16254 =
                                      let uu____16259 = p_scope orig  in
                                      mk_problem uu____16259 orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____16254
                                     in
                                  let uu____16264 =
                                    let uu____16269 =
                                      let uu____16270 =
                                        FStar_Syntax_Subst.compress k1'  in
                                      uu____16270.FStar_Syntax_Syntax.n  in
                                    let uu____16273 =
                                      let uu____16274 =
                                        FStar_Syntax_Subst.compress k2'  in
                                      uu____16274.FStar_Syntax_Syntax.n  in
                                    (uu____16269, uu____16273)  in
                                  (match uu____16264 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____16283,uu____16284) ->
                                       (k1'_xs, [sub_prob])
                                   | (uu____16287,FStar_Syntax_Syntax.Tm_type
                                      uu____16288) -> (k2'_ys, [sub_prob])
                                   | uu____16291 ->
                                       let uu____16296 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____16296 with
                                        | (t,uu____16308) ->
                                            let uu____16309 = new_uvar r zs t
                                               in
                                            (match uu____16309 with
                                             | (k_zs,uu____16321) ->
                                                 let kprob =
                                                   let uu____16323 =
                                                     let uu____16328 =
                                                       p_scope orig  in
                                                     mk_problem uu____16328
                                                       orig k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs
                                                       FStar_Pervasives_Native.None
                                                       "flex-flex kinding"
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_64  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_64) uu____16323
                                                    in
                                                 (k_zs, [sub_prob; kprob])))))
                          in
                       match uu____16168 with
                       | (k_u',sub_probs) ->
                           let uu____16341 =
                             let uu____16352 =
                               let uu____16353 = new_uvar r zs k_u'  in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____16353
                                in
                             let uu____16362 =
                               let uu____16365 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow xs1 uu____16365  in
                             let uu____16368 =
                               let uu____16371 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow ys1 uu____16371  in
                             (uu____16352, uu____16362, uu____16368)  in
                           (match uu____16341 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs  in
                                let uu____16390 =
                                  occurs_check env wl1 (u1, k1) sub1  in
                                (match uu____16390 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1)  in
                                        let uu____16409 =
                                          FStar_Syntax_Unionfind.equiv u1 u2
                                           in
                                        if uu____16409
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
                                           let uu____16413 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2
                                              in
                                           match uu____16413 with
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
             let solve_one_pat uu____16466 uu____16467 =
               match (uu____16466, uu____16467) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____16585 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____16585
                     then
                       let uu____16586 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____16587 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____16586 uu____16587
                     else ());
                    (let uu____16589 = FStar_Syntax_Unionfind.equiv u1 u2  in
                     if uu____16589
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16608  ->
                              fun uu____16609  ->
                                match (uu____16608, uu____16609) with
                                | ((a,uu____16627),(t21,uu____16629)) ->
                                    let uu____16638 =
                                      let uu____16643 = p_scope orig  in
                                      let uu____16644 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      mk_problem uu____16643 orig uu____16644
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index"
                                       in
                                    FStar_All.pipe_right uu____16638
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2
                          in
                       let guard =
                         let uu____16650 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____16650  in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl
                          in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2  in
                        let rhs_vars = FStar_Syntax_Free.names t21  in
                        let uu____16665 = occurs_check env wl (u1, k1) t21
                           in
                        match uu____16665 with
                        | (occurs_ok,uu____16673) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs  in
                            let uu____16681 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars)
                               in
                            if uu____16681
                            then
                              let sol =
                                let uu____16683 =
                                  let uu____16692 = u_abs k1 xs t21  in
                                  ((u1, k1), uu____16692)  in
                                TERM uu____16683  in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl
                                 in
                              solve env wl1
                            else
                              (let uu____16699 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok)
                                  in
                               if uu____16699
                               then
                                 let uu____16700 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2)
                                    in
                                 match uu____16700 with
                                 | FStar_Pervasives_Native.None  ->
                                     giveup_or_defer1 orig
                                       "flex-flex constraint"
                                 | FStar_Pervasives_Native.Some
                                     (sol,(uu____16724,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl
                                        in
                                     ((let uu____16750 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern")
                                          in
                                       if uu____16750
                                       then
                                         let uu____16751 =
                                           uvi_to_string env sol  in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16751
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16758 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint"))))
                in
             let uu____16760 = lhs  in
             match uu____16760 with
             | (t1,u1,k1,args1) ->
                 let uu____16765 = rhs  in
                 (match uu____16765 with
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
                       | uu____16805 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16815 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1)
                                 in
                              match uu____16815 with
                              | FStar_Pervasives_Native.None  ->
                                  giveup env
                                    "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                    orig
                              | FStar_Pervasives_Native.Some
                                  (sol,uu____16833) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl  in
                                  ((let uu____16840 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern")
                                       in
                                    if uu____16840
                                    then
                                      let uu____16841 = uvi_to_string env sol
                                         in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16841
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16848 ->
                                        giveup env "impossible" orig))))))
           in
        let orig = FStar_TypeChecker_Common.TProb problem  in
        let uu____16850 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs
           in
        if uu____16850
        then
          let uu____16851 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____16851
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs  in
           let t2 = problem.FStar_TypeChecker_Common.rhs  in
           let uu____16855 = FStar_Util.physical_equality t1 t2  in
           if uu____16855
           then
             let uu____16856 =
               solve_prob orig FStar_Pervasives_Native.None [] wl  in
             solve env uu____16856
           else
             ((let uu____16859 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck")
                  in
               if uu____16859
               then
                 let uu____16860 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid
                    in
                 FStar_Util.print1 "Attempting %s\n" uu____16860
               else ());
              (let r = FStar_TypeChecker_Env.get_range env  in
               let not_quote t =
                 let uu____16867 =
                   let uu____16868 = FStar_Syntax_Subst.compress t  in
                   uu____16868.FStar_Syntax_Syntax.n  in
                 match uu____16867 with
                 | FStar_Syntax_Syntax.Tm_meta
                     (uu____16871,FStar_Syntax_Syntax.Meta_quoted
                      uu____16872)
                     -> false
                 | uu____16883 -> true  in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_delayed uu____16884,uu____16885) ->
                   failwith "Impossible: terms were not compressed"
               | (uu____16910,FStar_Syntax_Syntax.Tm_delayed uu____16911) ->
                   failwith "Impossible: terms were not compressed"
               | (FStar_Syntax_Syntax.Tm_ascribed uu____16936,uu____16937) ->
                   let uu____16964 =
                     let uu___144_16965 = problem  in
                     let uu____16966 = FStar_Syntax_Util.unascribe t1  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___144_16965.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16966;
                       FStar_TypeChecker_Common.relation =
                         (uu___144_16965.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___144_16965.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___144_16965.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___144_16965.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___144_16965.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___144_16965.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___144_16965.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___144_16965.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____16964 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____16967,uu____16968) when
                   not_quote t1 ->
                   let uu____16975 =
                     let uu___145_16976 = problem  in
                     let uu____16977 = FStar_Syntax_Util.unmeta t1  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___145_16976.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____16977;
                       FStar_TypeChecker_Common.relation =
                         (uu___145_16976.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___145_16976.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___145_16976.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___145_16976.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___145_16976.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___145_16976.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___145_16976.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___145_16976.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____16975 wl
               | (uu____16978,FStar_Syntax_Syntax.Tm_ascribed uu____16979) ->
                   let uu____17006 =
                     let uu___146_17007 = problem  in
                     let uu____17008 = FStar_Syntax_Util.unascribe t2  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___146_17007.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___146_17007.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___146_17007.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____17008;
                       FStar_TypeChecker_Common.element =
                         (uu___146_17007.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___146_17007.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___146_17007.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___146_17007.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___146_17007.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___146_17007.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____17006 wl
               | (uu____17009,FStar_Syntax_Syntax.Tm_meta uu____17010) when
                   not_quote t2 ->
                   let uu____17017 =
                     let uu___147_17018 = problem  in
                     let uu____17019 = FStar_Syntax_Util.unmeta t2  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___147_17018.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___147_17018.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___147_17018.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____17019;
                       FStar_TypeChecker_Common.element =
                         (uu___147_17018.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___147_17018.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___147_17018.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___147_17018.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___147_17018.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___147_17018.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____17017 wl
               | (FStar_Syntax_Syntax.Tm_meta
                  (uu____17020,FStar_Syntax_Syntax.Meta_quoted
                   (t11,uu____17022)),FStar_Syntax_Syntax.Tm_meta
                  (uu____17023,FStar_Syntax_Syntax.Meta_quoted
                   (t21,uu____17025))) ->
                   let uu____17042 =
                     solve_prob orig FStar_Pervasives_Native.None [] wl  in
                   solve env uu____17042
               | (FStar_Syntax_Syntax.Tm_bvar uu____17043,uu____17044) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____17045,FStar_Syntax_Syntax.Tm_bvar uu____17046) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___108_17101 =
                     match uu___108_17101 with
                     | [] -> c
                     | bs ->
                         let uu____17123 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos
                            in
                         FStar_Syntax_Syntax.mk_Total uu____17123
                      in
                   let uu____17132 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                   (match uu____17132 with
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
                                   let uu____17274 =
                                     FStar_Options.use_eq_at_higher_order ()
                                      in
                                   if uu____17274
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation
                                    in
                                 let uu____17276 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____17276))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___109_17352 =
                     match uu___109_17352 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos
                      in
                   let uu____17386 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2))
                      in
                   (match uu____17386 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____17522 =
                                   let uu____17527 =
                                     FStar_Syntax_Subst.subst subst1 tbody11
                                      in
                                   let uu____17528 =
                                     FStar_Syntax_Subst.subst subst1 tbody21
                                      in
                                   mk_problem scope orig uu____17527
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____17528 FStar_Pervasives_Native.None
                                     "lambda co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____17522))
               | (FStar_Syntax_Syntax.Tm_abs uu____17533,uu____17534) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17559 -> true
                     | uu____17576 -> false  in
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
                       (let uu____17623 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___148_17631 = env  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___148_17631.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___148_17631.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___148_17631.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___148_17631.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___148_17631.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___148_17631.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___148_17631.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___148_17631.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___148_17631.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___148_17631.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___148_17631.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___148_17631.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___148_17631.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___148_17631.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___148_17631.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___148_17631.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___148_17631.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___148_17631.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___148_17631.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___148_17631.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___148_17631.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___148_17631.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___148_17631.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___148_17631.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___148_17631.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___148_17631.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___148_17631.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___148_17631.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___148_17631.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___148_17631.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___148_17631.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___148_17631.FStar_TypeChecker_Env.dep_graph)
                             }) t
                           in
                        match uu____17623 with
                        | (uu____17634,ty,uu____17636) ->
                            let uu____17637 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty
                               in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17637)
                      in
                   let uu____17638 =
                     let uu____17655 = maybe_eta t1  in
                     let uu____17662 = maybe_eta t2  in
                     (uu____17655, uu____17662)  in
                   (match uu____17638 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___149_17704 = problem  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___149_17704.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___149_17704.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___149_17704.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___149_17704.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___149_17704.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___149_17704.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___149_17704.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___149_17704.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17727 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____17727
                        then
                          let uu____17728 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____17728 t_abs wl
                        else
                          (let t11 = force_eta t1  in
                           let t21 = force_eta t2  in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___150_17743 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___150_17743.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___150_17743.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___150_17743.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___150_17743.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___150_17743.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___150_17743.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___150_17743.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___150_17743.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17767 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____17767
                        then
                          let uu____17768 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____17768 t_abs wl
                        else
                          (let t11 = force_eta t1  in
                           let t21 = force_eta t2  in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___150_17783 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___150_17783.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___150_17783.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___150_17783.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___150_17783.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___150_17783.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___150_17783.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___150_17783.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___150_17783.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17787 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17804,FStar_Syntax_Syntax.Tm_abs uu____17805) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17830 -> true
                     | uu____17847 -> false  in
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
                       (let uu____17894 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___148_17902 = env  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___148_17902.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___148_17902.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___148_17902.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___148_17902.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___148_17902.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___148_17902.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___148_17902.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___148_17902.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___148_17902.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___148_17902.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___148_17902.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___148_17902.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___148_17902.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___148_17902.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___148_17902.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___148_17902.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___148_17902.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___148_17902.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___148_17902.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___148_17902.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___148_17902.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___148_17902.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___148_17902.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___148_17902.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___148_17902.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___148_17902.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___148_17902.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___148_17902.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___148_17902.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___148_17902.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___148_17902.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___148_17902.FStar_TypeChecker_Env.dep_graph)
                             }) t
                           in
                        match uu____17894 with
                        | (uu____17905,ty,uu____17907) ->
                            let uu____17908 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty
                               in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17908)
                      in
                   let uu____17909 =
                     let uu____17926 = maybe_eta t1  in
                     let uu____17933 = maybe_eta t2  in
                     (uu____17926, uu____17933)  in
                   (match uu____17909 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___149_17975 = problem  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___149_17975.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___149_17975.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___149_17975.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___149_17975.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___149_17975.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___149_17975.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___149_17975.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___149_17975.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17998 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____17998
                        then
                          let uu____17999 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____17999 t_abs wl
                        else
                          (let t11 = force_eta t1  in
                           let t21 = force_eta t2  in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___150_18014 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___150_18014.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___150_18014.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___150_18014.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___150_18014.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___150_18014.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___150_18014.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___150_18014.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___150_18014.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____18038 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____18038
                        then
                          let uu____18039 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____18039 t_abs wl
                        else
                          (let t11 = force_eta t1  in
                           let t21 = force_eta t2  in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___150_18054 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___150_18054.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___150_18054.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___150_18054.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___150_18054.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___150_18054.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___150_18054.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___150_18054.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___150_18054.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____18058 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                   let should_delta =
                     ((let uu____18090 = FStar_Syntax_Free.uvars t1  in
                       FStar_Util.set_is_empty uu____18090) &&
                        (let uu____18102 = FStar_Syntax_Free.uvars t2  in
                         FStar_Util.set_is_empty uu____18102))
                       &&
                       (let uu____18117 =
                          head_matches env x1.FStar_Syntax_Syntax.sort
                            x2.FStar_Syntax_Syntax.sort
                           in
                        match uu____18117 with
                        | MisMatch
                            (FStar_Pervasives_Native.Some
                             d1,FStar_Pervasives_Native.Some d2)
                            ->
                            let is_unfoldable uu___110_18127 =
                              match uu___110_18127 with
                              | FStar_Syntax_Syntax.Delta_constant  -> true
                              | FStar_Syntax_Syntax.Delta_defined_at_level
                                  uu____18128 -> true
                              | uu____18129 -> false  in
                            (is_unfoldable d1) && (is_unfoldable d2)
                        | uu____18130 -> false)
                      in
                   let uu____18131 = as_refinement should_delta env wl t1  in
                   (match uu____18131 with
                    | (x11,phi1) ->
                        let uu____18138 =
                          as_refinement should_delta env wl t2  in
                        (match uu____18138 with
                         | (x21,phi21) ->
                             let base_prob =
                               let uu____18146 =
                                 let uu____18151 = p_scope orig  in
                                 mk_problem uu____18151 orig
                                   x11.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x21.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____18146
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
                               let uu____18185 = imp phi12 phi23  in
                               FStar_All.pipe_right uu____18185
                                 (guard_on_element wl problem x12)
                                in
                             let fallback uu____18189 =
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
                                 let uu____18195 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____18195 impl
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
                                 let uu____18204 =
                                   let uu____18209 =
                                     let uu____18210 = p_scope orig  in
                                     let uu____18217 =
                                       let uu____18224 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____18224]  in
                                     FStar_List.append uu____18210
                                       uu____18217
                                      in
                                   mk_problem uu____18209 orig phi11
                                     FStar_TypeChecker_Common.EQ phi22
                                     FStar_Pervasives_Native.None
                                     "refinement formula"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____18204
                                  in
                               let uu____18233 =
                                 solve env1
                                   (let uu___151_18235 = wl  in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___151_18235.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___151_18235.smt_ok);
                                      tcenv = (uu___151_18235.tcenv)
                                    })
                                  in
                               (match uu____18233 with
                                | Failed uu____18242 -> fallback ()
                                | Success uu____18247 ->
                                    let guard =
                                      let uu____18251 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      let uu____18256 =
                                        let uu____18257 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____18257
                                          (guard_on_element wl problem x12)
                                         in
                                      FStar_Syntax_Util.mk_conj uu____18251
                                        uu____18256
                                       in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl
                                       in
                                    let wl2 =
                                      let uu___152_18266 = wl1  in
                                      {
                                        attempting =
                                          (uu___152_18266.attempting);
                                        wl_deferred =
                                          (uu___152_18266.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___152_18266.defer_ok);
                                        smt_ok = (uu___152_18266.smt_ok);
                                        tcenv = (uu___152_18266.tcenv)
                                      }  in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18268,FStar_Syntax_Syntax.Tm_uvar uu____18269) ->
                   let uu____18302 = destruct_flex_t t1  in
                   let uu____18303 = destruct_flex_t t2  in
                   flex_flex1 orig uu____18302 uu____18303
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18304;
                     FStar_Syntax_Syntax.pos = uu____18305;
                     FStar_Syntax_Syntax.vars = uu____18306;_},uu____18307),FStar_Syntax_Syntax.Tm_uvar
                  uu____18308) ->
                   let uu____18361 = destruct_flex_t t1  in
                   let uu____18362 = destruct_flex_t t2  in
                   flex_flex1 orig uu____18361 uu____18362
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18363,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18364;
                     FStar_Syntax_Syntax.pos = uu____18365;
                     FStar_Syntax_Syntax.vars = uu____18366;_},uu____18367))
                   ->
                   let uu____18420 = destruct_flex_t t1  in
                   let uu____18421 = destruct_flex_t t2  in
                   flex_flex1 orig uu____18420 uu____18421
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18422;
                     FStar_Syntax_Syntax.pos = uu____18423;
                     FStar_Syntax_Syntax.vars = uu____18424;_},uu____18425),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18426;
                     FStar_Syntax_Syntax.pos = uu____18427;
                     FStar_Syntax_Syntax.vars = uu____18428;_},uu____18429))
                   ->
                   let uu____18502 = destruct_flex_t t1  in
                   let uu____18503 = destruct_flex_t t2  in
                   flex_flex1 orig uu____18502 uu____18503
               | (FStar_Syntax_Syntax.Tm_uvar uu____18504,uu____18505) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18522 = destruct_flex_pattern env t1  in
                   solve_t_flex_rigid false orig uu____18522 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18529;
                     FStar_Syntax_Syntax.pos = uu____18530;
                     FStar_Syntax_Syntax.vars = uu____18531;_},uu____18532),uu____18533)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18570 = destruct_flex_pattern env t1  in
                   solve_t_flex_rigid false orig uu____18570 t2 wl
               | (uu____18577,FStar_Syntax_Syntax.Tm_uvar uu____18578) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____18595,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18596;
                     FStar_Syntax_Syntax.pos = uu____18597;
                     FStar_Syntax_Syntax.vars = uu____18598;_},uu____18599))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18636,FStar_Syntax_Syntax.Tm_type uu____18637) ->
                   solve_t' env
                     (let uu___153_18655 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___153_18655.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___153_18655.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___153_18655.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___153_18655.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___153_18655.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___153_18655.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___153_18655.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___153_18655.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___153_18655.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18656;
                     FStar_Syntax_Syntax.pos = uu____18657;
                     FStar_Syntax_Syntax.vars = uu____18658;_},uu____18659),FStar_Syntax_Syntax.Tm_type
                  uu____18660) ->
                   solve_t' env
                     (let uu___153_18698 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___153_18698.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___153_18698.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___153_18698.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___153_18698.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___153_18698.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___153_18698.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___153_18698.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___153_18698.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___153_18698.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18699,FStar_Syntax_Syntax.Tm_arrow uu____18700) ->
                   solve_t' env
                     (let uu___153_18730 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___153_18730.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___153_18730.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___153_18730.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___153_18730.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___153_18730.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___153_18730.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___153_18730.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___153_18730.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___153_18730.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18731;
                     FStar_Syntax_Syntax.pos = uu____18732;
                     FStar_Syntax_Syntax.vars = uu____18733;_},uu____18734),FStar_Syntax_Syntax.Tm_arrow
                  uu____18735) ->
                   solve_t' env
                     (let uu___153_18785 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___153_18785.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___153_18785.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___153_18785.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___153_18785.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___153_18785.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___153_18785.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___153_18785.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___153_18785.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___153_18785.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18786,uu____18787) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation
                         in
                      let uu____18806 =
                        let uu____18807 = is_top_level_prob orig  in
                        FStar_All.pipe_left Prims.op_Negation uu____18807  in
                      if uu____18806
                      then
                        let uu____18808 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___154_18814 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___154_18814.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___154_18814.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___154_18814.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___154_18814.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___154_18814.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___154_18814.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___154_18814.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___154_18814.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___154_18814.FStar_TypeChecker_Common.rank)
                             })
                           in
                        let uu____18815 = destruct_flex_pattern env t1  in
                        solve_t_flex_rigid false uu____18808 uu____18815 t2
                          wl
                      else
                        (let uu____18823 = base_and_refinement env t2  in
                         match uu____18823 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18852 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___155_18858 = problem  in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___155_18858.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___155_18858.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___155_18858.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___155_18858.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___155_18858.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___155_18858.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___155_18858.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___155_18858.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___155_18858.FStar_TypeChecker_Common.rank)
                                       })
                                     in
                                  let uu____18859 =
                                    destruct_flex_pattern env t1  in
                                  solve_t_flex_rigid false uu____18852
                                    uu____18859 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___156_18873 = y  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___156_18873.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___156_18873.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }  in
                                  let impl =
                                    guard_on_element wl problem y' phi  in
                                  let base_prob =
                                    let uu____18876 =
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
                                      uu____18876
                                     in
                                  let guard =
                                    let uu____18888 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Util.mk_conj uu____18888
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
                       uu____18896;
                     FStar_Syntax_Syntax.pos = uu____18897;
                     FStar_Syntax_Syntax.vars = uu____18898;_},uu____18899),uu____18900)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation
                         in
                      let uu____18939 =
                        let uu____18940 = is_top_level_prob orig  in
                        FStar_All.pipe_left Prims.op_Negation uu____18940  in
                      if uu____18939
                      then
                        let uu____18941 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___154_18947 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___154_18947.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___154_18947.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___154_18947.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___154_18947.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___154_18947.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___154_18947.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___154_18947.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___154_18947.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___154_18947.FStar_TypeChecker_Common.rank)
                             })
                           in
                        let uu____18948 = destruct_flex_pattern env t1  in
                        solve_t_flex_rigid false uu____18941 uu____18948 t2
                          wl
                      else
                        (let uu____18956 = base_and_refinement env t2  in
                         match uu____18956 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18985 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___155_18991 = problem  in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___155_18991.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___155_18991.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___155_18991.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___155_18991.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___155_18991.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___155_18991.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___155_18991.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___155_18991.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___155_18991.FStar_TypeChecker_Common.rank)
                                       })
                                     in
                                  let uu____18992 =
                                    destruct_flex_pattern env t1  in
                                  solve_t_flex_rigid false uu____18985
                                    uu____18992 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___156_19006 = y  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___156_19006.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___156_19006.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }  in
                                  let impl =
                                    guard_on_element wl problem y' phi  in
                                  let base_prob =
                                    let uu____19009 =
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
                                      uu____19009
                                     in
                                  let guard =
                                    let uu____19021 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Util.mk_conj uu____19021
                                      impl
                                     in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl
                                     in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____19029,FStar_Syntax_Syntax.Tm_uvar uu____19030) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____19048 = base_and_refinement env t1  in
                      match uu____19048 with
                      | (t_base,uu____19060) ->
                          solve_t env
                            (let uu___157_19074 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___157_19074.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___157_19074.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___157_19074.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___157_19074.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___157_19074.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___157_19074.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___157_19074.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___157_19074.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____19075,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____19076;
                     FStar_Syntax_Syntax.pos = uu____19077;
                     FStar_Syntax_Syntax.vars = uu____19078;_},uu____19079))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____19117 = base_and_refinement env t1  in
                      match uu____19117 with
                      | (t_base,uu____19129) ->
                          solve_t env
                            (let uu___157_19143 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___157_19143.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___157_19143.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___157_19143.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___157_19143.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___157_19143.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___157_19143.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___157_19143.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___157_19143.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____19144,uu____19145) ->
                   let t21 =
                     let uu____19155 = base_and_refinement env t2  in
                     FStar_All.pipe_left force_refinement uu____19155  in
                   solve_t env
                     (let uu___158_19179 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___158_19179.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___158_19179.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___158_19179.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___158_19179.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___158_19179.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___158_19179.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___158_19179.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___158_19179.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___158_19179.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____19180,FStar_Syntax_Syntax.Tm_refine uu____19181) ->
                   let t11 =
                     let uu____19191 = base_and_refinement env t1  in
                     FStar_All.pipe_left force_refinement uu____19191  in
                   solve_t env
                     (let uu___159_19215 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___159_19215.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___159_19215.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___159_19215.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___159_19215.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___159_19215.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___159_19215.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___159_19215.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___159_19215.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___159_19215.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____19218,uu____19219) ->
                   let head1 =
                     let uu____19245 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19245
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19289 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19289
                       FStar_Pervasives_Native.fst
                      in
                   let uu____19330 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____19330
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____19345 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____19345
                      then
                        let guard =
                          let uu____19357 =
                            let uu____19358 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____19358 = FStar_Syntax_Util.Equal  in
                          if uu____19357
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19362 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____19362)
                           in
                        let uu____19365 = solve_prob orig guard [] wl  in
                        solve env uu____19365
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____19368,uu____19369) ->
                   let head1 =
                     let uu____19379 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19379
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19423 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19423
                       FStar_Pervasives_Native.fst
                      in
                   let uu____19464 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____19464
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____19479 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____19479
                      then
                        let guard =
                          let uu____19491 =
                            let uu____19492 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____19492 = FStar_Syntax_Util.Equal  in
                          if uu____19491
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19496 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____19496)
                           in
                        let uu____19499 = solve_prob orig guard [] wl  in
                        solve env uu____19499
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____19502,uu____19503) ->
                   let head1 =
                     let uu____19507 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19507
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19551 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19551
                       FStar_Pervasives_Native.fst
                      in
                   let uu____19592 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____19592
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____19607 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____19607
                      then
                        let guard =
                          let uu____19619 =
                            let uu____19620 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____19620 = FStar_Syntax_Util.Equal  in
                          if uu____19619
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19624 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____19624)
                           in
                        let uu____19627 = solve_prob orig guard [] wl  in
                        solve env uu____19627
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____19630,uu____19631) ->
                   let head1 =
                     let uu____19635 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19635
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19679 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19679
                       FStar_Pervasives_Native.fst
                      in
                   let uu____19720 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____19720
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____19735 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____19735
                      then
                        let guard =
                          let uu____19747 =
                            let uu____19748 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____19748 = FStar_Syntax_Util.Equal  in
                          if uu____19747
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19752 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____19752)
                           in
                        let uu____19755 = solve_prob orig guard [] wl  in
                        solve env uu____19755
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____19758,uu____19759) ->
                   let head1 =
                     let uu____19763 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19763
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19807 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19807
                       FStar_Pervasives_Native.fst
                      in
                   let uu____19848 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____19848
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____19863 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____19863
                      then
                        let guard =
                          let uu____19875 =
                            let uu____19876 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____19876 = FStar_Syntax_Util.Equal  in
                          if uu____19875
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____19880 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____19880)
                           in
                        let uu____19883 = solve_prob orig guard [] wl  in
                        solve env uu____19883
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____19886,uu____19887) ->
                   let head1 =
                     let uu____19905 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19905
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19949 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19949
                       FStar_Pervasives_Native.fst
                      in
                   let uu____19990 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____19990
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____20005 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____20005
                      then
                        let guard =
                          let uu____20017 =
                            let uu____20018 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____20018 = FStar_Syntax_Util.Equal  in
                          if uu____20017
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20022 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____20022)
                           in
                        let uu____20025 = solve_prob orig guard [] wl  in
                        solve env uu____20025
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20028,FStar_Syntax_Syntax.Tm_match uu____20029) ->
                   let head1 =
                     let uu____20055 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20055
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20099 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20099
                       FStar_Pervasives_Native.fst
                      in
                   let uu____20140 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____20140
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____20155 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____20155
                      then
                        let guard =
                          let uu____20167 =
                            let uu____20168 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____20168 = FStar_Syntax_Util.Equal  in
                          if uu____20167
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20172 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____20172)
                           in
                        let uu____20175 = solve_prob orig guard [] wl  in
                        solve env uu____20175
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20178,FStar_Syntax_Syntax.Tm_uinst uu____20179) ->
                   let head1 =
                     let uu____20189 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20189
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20233 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20233
                       FStar_Pervasives_Native.fst
                      in
                   let uu____20274 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____20274
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____20289 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____20289
                      then
                        let guard =
                          let uu____20301 =
                            let uu____20302 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____20302 = FStar_Syntax_Util.Equal  in
                          if uu____20301
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20306 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_83  ->
                                  FStar_Pervasives_Native.Some _0_83)
                               uu____20306)
                           in
                        let uu____20309 = solve_prob orig guard [] wl  in
                        solve env uu____20309
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20312,FStar_Syntax_Syntax.Tm_name uu____20313) ->
                   let head1 =
                     let uu____20317 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20317
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20361 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20361
                       FStar_Pervasives_Native.fst
                      in
                   let uu____20402 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____20402
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____20417 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____20417
                      then
                        let guard =
                          let uu____20429 =
                            let uu____20430 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____20430 = FStar_Syntax_Util.Equal  in
                          if uu____20429
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20434 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_Pervasives_Native.Some _0_84)
                               uu____20434)
                           in
                        let uu____20437 = solve_prob orig guard [] wl  in
                        solve env uu____20437
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20440,FStar_Syntax_Syntax.Tm_constant uu____20441) ->
                   let head1 =
                     let uu____20445 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20445
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20489 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20489
                       FStar_Pervasives_Native.fst
                      in
                   let uu____20530 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____20530
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____20545 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____20545
                      then
                        let guard =
                          let uu____20557 =
                            let uu____20558 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____20558 = FStar_Syntax_Util.Equal  in
                          if uu____20557
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20562 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_85  ->
                                  FStar_Pervasives_Native.Some _0_85)
                               uu____20562)
                           in
                        let uu____20565 = solve_prob orig guard [] wl  in
                        solve env uu____20565
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20568,FStar_Syntax_Syntax.Tm_fvar uu____20569) ->
                   let head1 =
                     let uu____20573 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20573
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20617 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20617
                       FStar_Pervasives_Native.fst
                      in
                   let uu____20658 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____20658
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____20673 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____20673
                      then
                        let guard =
                          let uu____20685 =
                            let uu____20686 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____20686 = FStar_Syntax_Util.Equal  in
                          if uu____20685
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20690 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_86  ->
                                  FStar_Pervasives_Native.Some _0_86)
                               uu____20690)
                           in
                        let uu____20693 = solve_prob orig guard [] wl  in
                        solve env uu____20693
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____20696,FStar_Syntax_Syntax.Tm_app uu____20697) ->
                   let head1 =
                     let uu____20715 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20715
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20759 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20759
                       FStar_Pervasives_Native.fst
                      in
                   let uu____20800 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____20800
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____20815 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____20815
                      then
                        let guard =
                          let uu____20827 =
                            let uu____20828 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____20828 = FStar_Syntax_Util.Equal  in
                          if uu____20827
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____20832 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_87  ->
                                  FStar_Pervasives_Native.Some _0_87)
                               uu____20832)
                           in
                        let uu____20835 = solve_prob orig guard [] wl  in
                        solve env uu____20835
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let
                  uu____20838,FStar_Syntax_Syntax.Tm_let uu____20839) ->
                   let uu____20864 = FStar_Syntax_Util.term_eq t1 t2  in
                   if uu____20864
                   then
                     let uu____20865 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl  in
                     solve env uu____20865
                   else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
               | (FStar_Syntax_Syntax.Tm_let uu____20867,uu____20868) ->
                   let uu____20881 =
                     let uu____20886 =
                       let uu____20887 = FStar_Syntax_Print.tag_of_term t1
                          in
                       let uu____20888 = FStar_Syntax_Print.tag_of_term t2
                          in
                       let uu____20889 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____20890 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format4
                         "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                         uu____20887 uu____20888 uu____20889 uu____20890
                        in
                     (FStar_Errors.Fatal_UnificationNotWellFormed,
                       uu____20886)
                      in
                   FStar_Errors.raise_error uu____20881
                     t1.FStar_Syntax_Syntax.pos
               | (uu____20891,FStar_Syntax_Syntax.Tm_let uu____20892) ->
                   let uu____20905 =
                     let uu____20910 =
                       let uu____20911 = FStar_Syntax_Print.tag_of_term t1
                          in
                       let uu____20912 = FStar_Syntax_Print.tag_of_term t2
                          in
                       let uu____20913 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____20914 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format4
                         "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                         uu____20911 uu____20912 uu____20913 uu____20914
                        in
                     (FStar_Errors.Fatal_UnificationNotWellFormed,
                       uu____20910)
                      in
                   FStar_Errors.raise_error uu____20905
                     t1.FStar_Syntax_Syntax.pos
               | uu____20915 -> giveup env "head tag mismatch" orig)))

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
          let uu____20943 = p_scope orig  in
          mk_problem uu____20943 orig t1 rel t2 FStar_Pervasives_Native.None
            reason
           in
        let solve_eq c1_comp c2_comp =
          (let uu____20952 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____20952
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____20954 =
               let uu____20955 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____20956 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20955 uu____20956
                in
             giveup env uu____20954 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____20976  ->
                    fun uu____20977  ->
                      match (uu____20976, uu____20977) with
                      | ((a1,uu____20995),(a2,uu____20997)) ->
                          let uu____21006 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg"
                             in
                          FStar_All.pipe_left
                            (fun _0_88  ->
                               FStar_TypeChecker_Common.TProb _0_88)
                            uu____21006)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args
                in
             let guard =
               let uu____21016 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs
                  in
               FStar_Syntax_Util.mk_conj_l uu____21016  in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl  in
             solve env (attempt sub_probs wl1))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____21040 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____21047)::[] -> wp1
              | uu____21064 ->
                  let uu____21073 =
                    let uu____21074 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name)
                       in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____21074
                     in
                  failwith uu____21073
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____21082 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____21082]
              | x -> x  in
            let uu____21084 =
              let uu____21093 =
                let uu____21094 =
                  let uu____21095 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____21095 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____21094  in
              [uu____21093]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____21084;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____21096 = lift_c1 ()  in solve_eq uu____21096 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___111_21102  ->
                       match uu___111_21102 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____21103 -> false))
                in
             let uu____21104 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____21138)::uu____21139,(wp2,uu____21141)::uu____21142)
                   -> (wp1, wp2)
               | uu____21199 ->
                   let uu____21220 =
                     let uu____21225 =
                       let uu____21226 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____21227 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____21226 uu____21227
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____21225)
                      in
                   FStar_Errors.raise_error uu____21220
                     env.FStar_TypeChecker_Env.range
                in
             match uu____21104 with
             | (wpc1,wpc2) ->
                 let uu____21246 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____21246
                 then
                   let uu____21249 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____21249 wl
                 else
                   (let uu____21253 =
                      let uu____21260 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____21260  in
                    match uu____21253 with
                    | (c2_decl,qualifiers) ->
                        let uu____21281 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____21281
                        then
                          let c1_repr =
                            let uu____21285 =
                              let uu____21286 =
                                let uu____21287 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____21287  in
                              let uu____21288 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21286 uu____21288
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21285
                             in
                          let c2_repr =
                            let uu____21290 =
                              let uu____21291 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____21292 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21291 uu____21292
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21290
                             in
                          let prob =
                            let uu____21294 =
                              let uu____21299 =
                                let uu____21300 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____21301 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____21300
                                  uu____21301
                                 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____21299
                               in
                            FStar_TypeChecker_Common.TProb uu____21294  in
                          let wl1 =
                            let uu____21303 =
                              let uu____21306 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_Pervasives_Native.Some uu____21306  in
                            solve_prob orig uu____21303 [] wl  in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____21315 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21315
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____21318 =
                                     let uu____21321 =
                                       let uu____21322 =
                                         let uu____21337 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____21338 =
                                           let uu____21341 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____21342 =
                                             let uu____21345 =
                                               let uu____21346 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____21346
                                                in
                                             [uu____21345]  in
                                           uu____21341 :: uu____21342  in
                                         (uu____21337, uu____21338)  in
                                       FStar_Syntax_Syntax.Tm_app uu____21322
                                        in
                                     FStar_Syntax_Syntax.mk uu____21321  in
                                   uu____21318 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____21355 =
                                    let uu____21358 =
                                      let uu____21359 =
                                        let uu____21374 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____21375 =
                                          let uu____21378 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____21379 =
                                            let uu____21382 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____21383 =
                                              let uu____21386 =
                                                let uu____21387 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____21387
                                                 in
                                              [uu____21386]  in
                                            uu____21382 :: uu____21383  in
                                          uu____21378 :: uu____21379  in
                                        (uu____21374, uu____21375)  in
                                      FStar_Syntax_Syntax.Tm_app uu____21359
                                       in
                                    FStar_Syntax_Syntax.mk uu____21358  in
                                  uu____21355 FStar_Pervasives_Native.None r)
                              in
                           let base_prob =
                             let uu____21394 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type"
                                in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____21394
                              in
                           let wl1 =
                             let uu____21404 =
                               let uu____21407 =
                                 let uu____21410 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____21410 g  in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____21407
                                in
                             solve_prob orig uu____21404 [] wl  in
                           solve env (attempt [base_prob] wl1))))
           in
        let uu____21423 = FStar_Util.physical_equality c1 c2  in
        if uu____21423
        then
          let uu____21424 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____21424
        else
          ((let uu____21427 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____21427
            then
              let uu____21428 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____21429 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____21428
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____21429
            else ());
           (let uu____21431 =
              let uu____21436 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____21437 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____21436, uu____21437)  in
            match uu____21431 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21441),FStar_Syntax_Syntax.Total
                    (t2,uu____21443)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21460 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21460 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21463,FStar_Syntax_Syntax.Total uu____21464) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21482),FStar_Syntax_Syntax.Total
                    (t2,uu____21484)) ->
                     let uu____21501 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21501 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21505),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21507)) ->
                     let uu____21524 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21524 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21528),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21530)) ->
                     let uu____21547 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21547 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21550,FStar_Syntax_Syntax.Comp uu____21551) ->
                     let uu____21560 =
                       let uu___160_21565 = problem  in
                       let uu____21570 =
                         let uu____21571 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21571
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___160_21565.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21570;
                         FStar_TypeChecker_Common.relation =
                           (uu___160_21565.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___160_21565.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___160_21565.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___160_21565.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___160_21565.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___160_21565.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___160_21565.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___160_21565.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21560 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21572,FStar_Syntax_Syntax.Comp uu____21573) ->
                     let uu____21582 =
                       let uu___160_21587 = problem  in
                       let uu____21592 =
                         let uu____21593 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21593
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___160_21587.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21592;
                         FStar_TypeChecker_Common.relation =
                           (uu___160_21587.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___160_21587.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___160_21587.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___160_21587.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___160_21587.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___160_21587.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___160_21587.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___160_21587.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21582 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21594,FStar_Syntax_Syntax.GTotal uu____21595) ->
                     let uu____21604 =
                       let uu___161_21609 = problem  in
                       let uu____21614 =
                         let uu____21615 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21615
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___161_21609.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___161_21609.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___161_21609.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21614;
                         FStar_TypeChecker_Common.element =
                           (uu___161_21609.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___161_21609.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___161_21609.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___161_21609.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___161_21609.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___161_21609.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21604 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21616,FStar_Syntax_Syntax.Total uu____21617) ->
                     let uu____21626 =
                       let uu___161_21631 = problem  in
                       let uu____21636 =
                         let uu____21637 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21637
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___161_21631.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___161_21631.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___161_21631.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21636;
                         FStar_TypeChecker_Common.element =
                           (uu___161_21631.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___161_21631.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___161_21631.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___161_21631.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___161_21631.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___161_21631.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21626 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21638,FStar_Syntax_Syntax.Comp uu____21639) ->
                     let uu____21640 =
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
                     if uu____21640
                     then
                       let uu____21641 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____21641 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21647 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21657 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____21658 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____21657, uu____21658))
                             in
                          match uu____21647 with
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
                           (let uu____21665 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____21665
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21667 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____21667 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21670 =
                                  let uu____21671 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____21672 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____21671 uu____21672
                                   in
                                giveup env uu____21670 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____21677 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21715  ->
              match uu____21715 with
              | (uu____21728,uu____21729,u,uu____21731,uu____21732,uu____21733)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____21677 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____21764 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____21764 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____21782 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21810  ->
                match uu____21810 with
                | (u1,u2) ->
                    let uu____21817 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____21818 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____21817 uu____21818))
         in
      FStar_All.pipe_right uu____21782 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21835,[])) -> "{}"
      | uu____21860 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21877 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____21877
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____21880 =
              FStar_List.map
                (fun uu____21890  ->
                   match uu____21890 with
                   | (uu____21895,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____21880 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____21900 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21900 imps
  
let new_t_problem :
  'Auu____21908 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____21908 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____21908)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____21942 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel")
                   in
                if uu____21942
                then
                  let uu____21943 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs  in
                  let uu____21944 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs  in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21943
                    (rel_to_string rel) uu____21944
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
            let uu____21968 =
              let uu____21971 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____21971
               in
            FStar_Syntax_Syntax.new_bv uu____21968 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____21980 =
              let uu____21983 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____21983
               in
            let uu____21986 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____21980 uu____21986  in
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
          let uu____22016 = FStar_Options.eager_inference ()  in
          if uu____22016
          then
            let uu___162_22017 = probs  in
            {
              attempting = (uu___162_22017.attempting);
              wl_deferred = (uu___162_22017.wl_deferred);
              ctr = (uu___162_22017.ctr);
              defer_ok = false;
              smt_ok = (uu___162_22017.smt_ok);
              tcenv = (uu___162_22017.tcenv)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            ((let uu____22028 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____22028
              then
                let uu____22029 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____22029
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
          ((let uu____22043 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____22043
            then
              let uu____22044 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____22044
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____22048 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____22048
             then
               let uu____22049 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____22049
             else ());
            (let f2 =
               let uu____22052 =
                 let uu____22053 = FStar_Syntax_Util.unmeta f1  in
                 uu____22053.FStar_Syntax_Syntax.n  in
               match uu____22052 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____22057 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___163_22058 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___163_22058.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___163_22058.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___163_22058.FStar_TypeChecker_Env.implicits)
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
            let uu____22077 =
              let uu____22078 =
                let uu____22079 =
                  let uu____22080 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____22080
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____22079;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____22078  in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____22077
  
let with_guard_no_simp :
  'Auu____22107 .
    'Auu____22107 ->
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
            let uu____22127 =
              let uu____22128 =
                let uu____22129 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____22129
                  (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____22128;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____22127
  
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
          (let uu____22167 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____22167
           then
             let uu____22168 = FStar_Syntax_Print.term_to_string t1  in
             let uu____22169 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____22168
               uu____22169
           else ());
          (let prob =
             let uu____22172 =
               let uu____22177 = FStar_TypeChecker_Env.get_range env  in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____22177
                in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____22172
              in
           let g =
             let uu____22185 =
               let uu____22188 = singleton' env prob smt_ok  in
               solve_and_commit env uu____22188
                 (fun uu____22190  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob) uu____22185  in
           g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22208 = try_teq true env t1 t2  in
        match uu____22208 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____22212 = FStar_TypeChecker_Env.get_range env  in
              let uu____22213 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____22212 uu____22213);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____22220 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____22220
              then
                let uu____22221 = FStar_Syntax_Print.term_to_string t1  in
                let uu____22222 = FStar_Syntax_Print.term_to_string t2  in
                let uu____22223 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____22221
                  uu____22222 uu____22223
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
          let uu____22237 = FStar_TypeChecker_Env.get_range env  in
          let uu____22238 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____22237 uu____22238
  
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____22255 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22255
         then
           let uu____22256 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____22257 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____22256
             uu____22257
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB  in
         let prob =
           let uu____22262 =
             let uu____22267 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____22267 "sub_comp"
              in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____22262
            in
         let uu____22272 =
           let uu____22275 = singleton env prob  in
           solve_and_commit env uu____22275
             (fun uu____22277  -> FStar_Pervasives_Native.None)
            in
         FStar_All.pipe_left (with_guard env prob) uu____22272)
  
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
      fun uu____22306  ->
        match uu____22306 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22345 =
                 let uu____22350 =
                   let uu____22351 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____22352 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____22351 uu____22352
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____22350)  in
               let uu____22353 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____22345 uu____22353)
               in
            let equiv1 v1 v' =
              let uu____22361 =
                let uu____22366 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____22367 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____22366, uu____22367)  in
              match uu____22361 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22386 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22416 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____22416 with
                      | FStar_Syntax_Syntax.U_unif uu____22423 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22452  ->
                                    match uu____22452 with
                                    | (u,v') ->
                                        let uu____22461 = equiv1 v1 v'  in
                                        if uu____22461
                                        then
                                          let uu____22464 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____22464 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____22480 -> []))
               in
            let uu____22485 =
              let wl =
                let uu___164_22489 = empty_worklist env  in
                {
                  attempting = (uu___164_22489.attempting);
                  wl_deferred = (uu___164_22489.wl_deferred);
                  ctr = (uu___164_22489.ctr);
                  defer_ok = false;
                  smt_ok = (uu___164_22489.smt_ok);
                  tcenv = (uu___164_22489.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22507  ->
                      match uu____22507 with
                      | (lb,v1) ->
                          let uu____22514 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____22514 with
                           | USolved wl1 -> ()
                           | uu____22516 -> fail lb v1)))
               in
            let rec check_ineq uu____22524 =
              match uu____22524 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22533) -> true
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
                      uu____22556,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22558,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22569) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22576,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22584 -> false)
               in
            let uu____22589 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22604  ->
                      match uu____22604 with
                      | (u,v1) ->
                          let uu____22611 = check_ineq (u, v1)  in
                          if uu____22611
                          then true
                          else
                            ((let uu____22614 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____22614
                              then
                                let uu____22615 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____22616 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____22615
                                  uu____22616
                              else ());
                             false)))
               in
            if uu____22589
            then ()
            else
              ((let uu____22620 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____22620
                then
                  ((let uu____22622 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22622);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22632 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22632))
                else ());
               (let uu____22642 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____22642))
  
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
      let fail uu____22690 =
        match uu____22690 with
        | (d,s) ->
            let msg = explain env d s  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
              (p_loc d)
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____22704 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____22704
       then
         let uu____22705 = wl_to_string wl  in
         let uu____22706 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits)
            in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22705 uu____22706
       else ());
      (let g1 =
         let uu____22721 = solve_and_commit env wl fail  in
         match uu____22721 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___165_22734 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___165_22734.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___165_22734.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___165_22734.FStar_TypeChecker_Env.implicits)
             }
         | uu____22739 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___166_22743 = g1  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___166_22743.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___166_22743.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___166_22743.FStar_TypeChecker_Env.implicits)
        }))
  
let (last_proof_ns :
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (maybe_update_proof_ns : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns  in
    let uu____22769 = FStar_ST.op_Bang last_proof_ns  in
    match uu____22769 with
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
            let uu___167_22872 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___167_22872.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___167_22872.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___167_22872.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____22873 =
            let uu____22874 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____22874  in
          if uu____22873
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22882 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____22883 =
                       let uu____22884 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22884
                        in
                     FStar_Errors.diag uu____22882 uu____22883)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____22888 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____22889 =
                        let uu____22890 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22890
                         in
                      FStar_Errors.diag uu____22888 uu____22889)
                   else ();
                   (let uu____22893 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in uu____22893 "discharge_guard'" env
                      vc1);
                   (let uu____22894 = check_trivial vc1  in
                    match uu____22894 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22901 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22902 =
                                let uu____22903 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22903
                                 in
                              FStar_Errors.diag uu____22901 uu____22902)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22908 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22909 =
                                let uu____22910 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22910
                                 in
                              FStar_Errors.diag uu____22908 uu____22909)
                           else ();
                           (let vcs =
                              let uu____22921 = FStar_Options.use_tactics ()
                                 in
                              if uu____22921
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22940  ->
                                     (let uu____22942 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left
                                        FStar_Pervasives.ignore uu____22942);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____22944 =
                                   let uu____22951 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____22951)  in
                                 [uu____22944])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22985  ->
                                    match uu____22985 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal
                                           in
                                        let uu____22996 = check_trivial goal1
                                           in
                                        (match uu____22996 with
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
                                                (let uu____23004 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____23005 =
                                                   let uu____23006 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   let uu____23007 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____23006 uu____23007
                                                    in
                                                 FStar_Errors.diag
                                                   uu____23004 uu____23005)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____23010 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____23011 =
                                                   let uu____23012 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____23012
                                                    in
                                                 FStar_Errors.diag
                                                   uu____23010 uu____23011)
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
      let uu____23022 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23022 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____23028 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____23028
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____23035 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____23035 with
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
          let uu____23054 = FStar_Syntax_Unionfind.find u  in
          match uu____23054 with
          | FStar_Pervasives_Native.None  -> true
          | uu____23057 -> false  in
        let rec until_fixpoint acc implicits =
          let uu____23075 = acc  in
          match uu____23075 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____23161 = hd1  in
                   (match uu____23161 with
                    | (uu____23174,env,u,tm,k,r) ->
                        let uu____23180 = unresolved u  in
                        if uu____23180
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env tm
                              in
                           let env1 =
                             if forcelax
                             then
                               let uu___168_23210 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___168_23210.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___168_23210.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___168_23210.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___168_23210.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___168_23210.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___168_23210.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___168_23210.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___168_23210.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___168_23210.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___168_23210.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___168_23210.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___168_23210.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___168_23210.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___168_23210.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___168_23210.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___168_23210.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___168_23210.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___168_23210.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___168_23210.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___168_23210.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___168_23210.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___168_23210.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___168_23210.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___168_23210.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___168_23210.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___168_23210.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___168_23210.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___168_23210.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___168_23210.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___168_23210.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___168_23210.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___168_23210.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___168_23210.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___168_23210.FStar_TypeChecker_Env.dep_graph)
                               }
                             else env  in
                           (let uu____23213 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck")
                               in
                            if uu____23213
                            then
                              let uu____23214 =
                                FStar_Syntax_Print.uvar_to_string u  in
                              let uu____23215 =
                                FStar_Syntax_Print.term_to_string tm1  in
                              let uu____23216 =
                                FStar_Syntax_Print.term_to_string k  in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____23214 uu____23215 uu____23216
                            else ());
                           (let g1 =
                              try
                                env1.FStar_TypeChecker_Env.check_type_of
                                  must_total env1 tm1 k
                              with
                              | e ->
                                  ((let uu____23227 =
                                      let uu____23236 =
                                        let uu____23243 =
                                          let uu____23244 =
                                            FStar_Syntax_Print.uvar_to_string
                                              u
                                             in
                                          let uu____23245 =
                                            FStar_TypeChecker_Normalize.term_to_string
                                              env1 tm1
                                             in
                                          FStar_Util.format2
                                            "Failed while checking implicit %s set to %s"
                                            uu____23244 uu____23245
                                           in
                                        (FStar_Errors.Error_BadImplicit,
                                          uu____23243, r)
                                         in
                                      [uu____23236]  in
                                    FStar_Errors.add_errors uu____23227);
                                   FStar_Exn.raise e)
                               in
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___171_23259 = g1  in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___171_23259.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___171_23259.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___171_23259.FStar_TypeChecker_Env.implicits)
                                }
                              else g1  in
                            let g' =
                              let uu____23262 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____23268  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true
                                 in
                              match uu____23262 with
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
        let uu___172_23296 = g  in
        let uu____23297 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___172_23296.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___172_23296.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___172_23296.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____23297
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
        let uu____23351 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____23351 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23364 = discharge_guard env g1  in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____23364
      | (reason,uu____23366,uu____23367,e,t,r)::uu____23371 ->
          let uu____23398 =
            let uu____23403 =
              let uu____23404 = FStar_Syntax_Print.term_to_string t  in
              let uu____23405 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format2
                "Failed to resolve implicit argument of type '%s' introduced in %s"
                uu____23404 uu____23405
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____23403)
             in
          FStar_Errors.raise_error uu____23398 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___173_23412 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___173_23412.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___173_23412.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___173_23412.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____23435 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23435 with
      | FStar_Pervasives_Native.Some uu____23440 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23450 = try_teq false env t1 t2  in
        match uu____23450 with
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
        (let uu____23470 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23470
         then
           let uu____23471 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23472 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23471
             uu____23472
         else ());
        (let uu____23474 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____23474 with
         | (prob,x) ->
             let g =
               let uu____23490 =
                 let uu____23493 = singleton' env prob true  in
                 solve_and_commit env uu____23493
                   (fun uu____23495  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23490  in
             ((let uu____23505 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____23505
               then
                 let uu____23506 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____23507 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____23508 =
                   let uu____23509 = FStar_Util.must g  in
                   guard_to_string env uu____23509  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23506 uu____23507 uu____23508
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
        let uu____23537 = check_subtyping env t1 t2  in
        match uu____23537 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23556 =
              let uu____23557 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____23557 g  in
            FStar_Pervasives_Native.Some uu____23556
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23569 = check_subtyping env t1 t2  in
        match uu____23569 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23588 =
              let uu____23589 =
                let uu____23590 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____23590]  in
              close_guard env uu____23589 g  in
            FStar_Pervasives_Native.Some uu____23588
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23601 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23601
         then
           let uu____23602 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23603 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23602
             uu____23603
         else ());
        (let uu____23605 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____23605 with
         | (prob,x) ->
             let g =
               let uu____23615 =
                 let uu____23618 = singleton' env prob false  in
                 solve_and_commit env uu____23618
                   (fun uu____23620  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23615  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23631 =
                      let uu____23632 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____23632]  in
                    close_guard env uu____23631 g1  in
                  discharge_guard_nosmt env g2))
  