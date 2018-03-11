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
          let uu___116_91 = g  in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___116_91.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___116_91.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___116_91.FStar_TypeChecker_Env.implicits)
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
          let uu___117_168 = g  in
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
              (uu___117_168.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___117_168.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___117_168.FStar_TypeChecker_Env.implicits)
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
          let uu___118_211 = g  in
          let uu____212 =
            let uu____213 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____213  in
          {
            FStar_TypeChecker_Env.guard_f = uu____212;
            FStar_TypeChecker_Env.deferred =
              (uu___118_211.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___118_211.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___118_211.FStar_TypeChecker_Env.implicits)
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
            let uu___119_337 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___119_337.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___119_337.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___119_337.FStar_TypeChecker_Env.implicits)
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
            let uu___120_369 = g  in
            let uu____370 =
              let uu____371 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____371  in
            {
              FStar_TypeChecker_Env.guard_f = uu____370;
              FStar_TypeChecker_Env.deferred =
                (uu___120_369.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___120_369.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___120_369.FStar_TypeChecker_Env.implicits)
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
  fun uu___86_805  ->
    match uu___86_805 with
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
    fun uu___87_902  ->
      match uu___87_902 with
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
    fun uu___88_936  ->
      match uu___88_936 with
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
        let uu___121_1056 = empty_worklist env  in
        {
          attempting = [prob];
          wl_deferred = (uu___121_1056.wl_deferred);
          ctr = (uu___121_1056.ctr);
          defer_ok = (uu___121_1056.defer_ok);
          smt_ok;
          tcenv = (uu___121_1056.tcenv)
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
      let uu___122_1087 = empty_worklist env  in
      let uu____1088 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1088;
        wl_deferred = (uu___122_1087.wl_deferred);
        ctr = (uu___122_1087.ctr);
        defer_ok = false;
        smt_ok = (uu___122_1087.smt_ok);
        tcenv = (uu___122_1087.tcenv)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___123_1102 = wl  in
        {
          attempting = (uu___123_1102.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___123_1102.ctr);
          defer_ok = (uu___123_1102.defer_ok);
          smt_ok = (uu___123_1102.smt_ok);
          tcenv = (uu___123_1102.tcenv)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      let uu___124_1119 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___124_1119.wl_deferred);
        ctr = (uu___124_1119.ctr);
        defer_ok = (uu___124_1119.defer_ok);
        smt_ok = (uu___124_1119.smt_ok);
        tcenv = (uu___124_1119.tcenv)
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
  fun uu___89_1135  ->
    match uu___89_1135 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1139 'Auu____1140 .
    ('Auu____1139,'Auu____1140) FStar_TypeChecker_Common.problem ->
      ('Auu____1139,'Auu____1140) FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___125_1157 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___125_1157.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___125_1157.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___125_1157.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.scope =
        (uu___125_1157.FStar_TypeChecker_Common.scope);
      FStar_TypeChecker_Common.reason =
        (uu___125_1157.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___125_1157.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___125_1157.FStar_TypeChecker_Common.rank)
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
  fun uu___90_1186  ->
    match uu___90_1186 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.CProb _0_42)
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___91_1210  ->
      match uu___91_1210 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___92_1213  ->
    match uu___92_1213 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___93_1226  ->
    match uu___93_1226 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___94_1241  ->
    match uu___94_1241 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___95_1256  ->
    match uu___95_1256 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_guard :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___96_1273  ->
    match uu___96_1273 with
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
  fun uu___97_1322  ->
    match uu___97_1322 with
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
         (fun uu___98_1686  ->
            match uu___98_1686 with
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
        (fun uu___99_1721  ->
           match uu___99_1721 with
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
        (fun uu___100_1756  ->
           match uu___100_1756 with
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
                    let uu___126_1848 = x  in
                    let uu____1849 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___126_1848.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___126_1848.FStar_Syntax_Syntax.index);
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
                 (let uu___127_3203 = wl  in
                  {
                    attempting = (uu___127_3203.attempting);
                    wl_deferred = (uu___127_3203.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___127_3203.defer_ok);
                    smt_ok = (uu___127_3203.smt_ok);
                    tcenv = (uu___127_3203.tcenv)
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
        (let uu___128_3228 = wl  in
         {
           attempting = (uu___128_3228.attempting);
           wl_deferred = (uu___128_3228.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___128_3228.defer_ok);
           smt_ok = (uu___128_3228.smt_ok);
           tcenv = (uu___128_3228.tcenv)
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
  
let string_of_option :
  'Auu____4815 .
    ('Auu____4815 -> Prims.string) ->
      'Auu____4815 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___101_4828  ->
      match uu___101_4828 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____4834 = f x  in Prims.strcat "Some " uu____4834
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___102_4837  ->
    match uu___102_4837 with
    | MisMatch (d1,d2) ->
        let uu____4848 =
          let uu____4849 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____4850 =
            let uu____4851 =
              let uu____4852 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____4852 ")"  in
            Prims.strcat ") (" uu____4851  in
          Prims.strcat uu____4849 uu____4850  in
        Prims.strcat "MisMatch (" uu____4848
    | HeadMatch  -> "HeadMatch"
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___103_4855  ->
    match uu___103_4855 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____4870 -> HeadMatch
  
let (and_match :
  match_result -> (Prims.unit -> match_result) -> match_result) =
  fun m1  ->
    fun m2  ->
      match m1 with
      | MisMatch (i,j) -> MisMatch (i, j)
      | HeadMatch  ->
          let uu____4896 = m2 ()  in
          (match uu____4896 with
           | MisMatch (i,j) -> MisMatch (i, j)
           | uu____4911 -> HeadMatch)
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____4920 ->
          let uu____4921 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____4921 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____4932 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____4951 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____4960 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____4988 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____4988
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____4989 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____4990 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____4991 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5008 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5021 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5045) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5051,uu____5052) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5094) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5115;
             FStar_Syntax_Syntax.index = uu____5116;
             FStar_Syntax_Syntax.sort = t2;_},uu____5118)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5125 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5126 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5127 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5140 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5158 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____5158
  
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
            let uu____5185 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____5185
            then FullMatch
            else
              (let uu____5187 =
                 let uu____5196 =
                   let uu____5199 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____5199  in
                 let uu____5200 =
                   let uu____5203 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____5203  in
                 (uu____5196, uu____5200)  in
               MisMatch uu____5187)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5209),FStar_Syntax_Syntax.Tm_uinst (g,uu____5211)) ->
            let uu____5220 = head_matches env f g  in
            FStar_All.pipe_right uu____5220 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5223 = FStar_Const.eq_const c d  in
            if uu____5223
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____5230),FStar_Syntax_Syntax.Tm_uvar (uv',uu____5232)) ->
            let uu____5281 = FStar_Syntax_Unionfind.equiv uv uv'  in
            if uu____5281
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5288),FStar_Syntax_Syntax.Tm_refine (y,uu____5290)) ->
            let uu____5299 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5299 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5301),uu____5302) ->
            let uu____5307 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____5307 head_match
        | (uu____5308,FStar_Syntax_Syntax.Tm_refine (x,uu____5310)) ->
            let uu____5315 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5315 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5316,FStar_Syntax_Syntax.Tm_type
           uu____5317) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5318,FStar_Syntax_Syntax.Tm_arrow uu____5319) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            if (FStar_List.length bs1) = (FStar_List.length bs2)
            then
              let uu____5448 =
                let uu____5449 = FStar_List.zip bs1 bs2  in
                let uu____5484 = head_matches env t12 t22  in
                FStar_List.fold_right
                  (fun uu____5493  ->
                     fun a  ->
                       match uu____5493 with
                       | (b1,b2) ->
                           and_match a
                             (fun uu____5502  -> branch_matches env b1 b2))
                  uu____5449 uu____5484
                 in
              FStar_All.pipe_right uu____5448 head_match
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5509),FStar_Syntax_Syntax.Tm_app (head',uu____5511))
            ->
            let uu____5552 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____5552 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____5554),uu____5555) ->
            let uu____5576 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____5576 head_match
        | (uu____5577,FStar_Syntax_Syntax.Tm_app (head1,uu____5579)) ->
            let uu____5600 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____5600 head_match
        | uu____5601 ->
            let uu____5606 =
              let uu____5615 = delta_depth_of_term env t11  in
              let uu____5618 = delta_depth_of_term env t21  in
              (uu____5615, uu____5618)  in
            MisMatch uu____5606

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
          | (uu____5670,uu____5671) -> false  in
        let uu____5680 = b1  in
        match uu____5680 with
        | (p1,w1,t1) ->
            let uu____5700 = b2  in
            (match uu____5700 with
             | (p2,w2,t2) ->
                 let uu____5720 = FStar_Syntax_Syntax.eq_pat p1 p2  in
                 if uu____5720
                 then
                   let uu____5721 =
                     (let uu____5724 = FStar_Syntax_Util.eq_tm t1 t2  in
                      uu____5724 = FStar_Syntax_Util.Equal) &&
                       (related_by
                          (fun t11  ->
                             fun t21  ->
                               let uu____5733 =
                                 FStar_Syntax_Util.eq_tm t11 t21  in
                               uu____5733 = FStar_Syntax_Util.Equal) w1 w2)
                      in
                   (if uu____5721
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
  'Auu____5749 .
    FStar_TypeChecker_Env.env ->
      'Auu____5749 ->
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
            let uu____5782 = FStar_Syntax_Util.head_and_args t  in
            match uu____5782 with
            | (head1,uu____5800) ->
                let uu____5821 =
                  let uu____5822 = FStar_Syntax_Util.un_uinst head1  in
                  uu____5822.FStar_Syntax_Syntax.n  in
                (match uu____5821 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____5828 =
                       let uu____5829 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       FStar_All.pipe_right uu____5829 FStar_Option.isSome
                        in
                     if uu____5828
                     then
                       let uu____5848 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t
                          in
                       FStar_All.pipe_right uu____5848
                         (fun _0_45  -> FStar_Pervasives_Native.Some _0_45)
                     else FStar_Pervasives_Native.None
                 | uu____5852 -> FStar_Pervasives_Native.None)
             in
          let success d r t11 t21 =
            (r,
              (if d > (Prims.parse_int "0")
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let fail1 r = (r, FStar_Pervasives_Native.None)  in
          let rec aux retry n_delta t11 t21 =
            let r = head_matches env t11 t21  in
            match r with
            | MisMatch
                (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ),uu____5955)
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____5973 =
                     let uu____5982 = maybe_inline t11  in
                     let uu____5985 = maybe_inline t21  in
                     (uu____5982, uu____5985)  in
                   match uu____5973 with
                   | (FStar_Pervasives_Native.None
                      ,FStar_Pervasives_Native.None ) -> fail1 r
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
                (uu____6022,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6040 =
                     let uu____6049 = maybe_inline t11  in
                     let uu____6052 = maybe_inline t21  in
                     (uu____6049, uu____6052)  in
                   match uu____6040 with
                   | (FStar_Pervasives_Native.None
                      ,FStar_Pervasives_Native.None ) -> fail1 r
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
                let uu____6095 = FStar_TypeChecker_Common.decr_delta_depth d1
                   in
                (match uu____6095 with
                 | FStar_Pervasives_Native.None  -> fail1 r
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
                let uu____6118 =
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
                (match uu____6118 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6142 -> fail1 r
            | uu____6151 -> success n_delta r t11 t21  in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____6164 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____6164
           then
             let uu____6165 = FStar_Syntax_Print.term_to_string t1  in
             let uu____6166 = FStar_Syntax_Print.term_to_string t2  in
             let uu____6167 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____6165
               uu____6166 uu____6167
           else ());
          r
  
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | C of FStar_Syntax_Syntax.comp [@@deriving show]
let (uu___is_T : tc -> Prims.bool) =
  fun projectee  -> match projectee with | T _0 -> true | uu____6207 -> false 
let (__proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | T _0 -> _0 
let (uu___is_C : tc -> Prims.bool) =
  fun projectee  -> match projectee with | C _0 -> true | uu____6243 -> false 
let (__proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp) =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list[@@deriving show]
let (tc_to_string : tc -> Prims.string) =
  fun uu___104_6255  ->
    match uu___104_6255 with
    | T (t,uu____6257) -> term_to_string t
    | C c -> FStar_Syntax_Print.comp_to_string c
  
let (generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6273 = FStar_Syntax_Util.type_u ()  in
      match uu____6273 with
      | (t,uu____6279) ->
          let uu____6280 = new_uvar r binders t  in
          FStar_Pervasives_Native.fst uu____6280
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6291 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____6291 FStar_Pervasives_Native.fst
  
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
        let uu____6355 = head_matches env t1 t'  in
        match uu____6355 with
        | MisMatch uu____6356 -> false
        | uu____6365 -> true  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____6461,imp),T (t2,uu____6464)) -> (t2, imp)
                     | uu____6483 -> failwith "Bad reconstruction") args
                args'
               in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____6550  ->
                    match uu____6550 with
                    | (t2,uu____6564) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____6607 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____6607 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____6682))::tcs2) ->
                       aux
                         (((let uu___129_6717 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___129_6717.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___129_6717.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____6735 -> failwith "Bad reconstruction"  in
                 aux [] bs1 tcs  in
               let rec decompose1 out uu___105_6788 =
                 match uu___105_6788 with
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
               let uu____6905 = decompose1 [] bs1  in
               (rebuild, matches, uu____6905))
      | uu____6954 ->
          let rebuild uu___106_6960 =
            match uu___106_6960 with
            | [] -> t1
            | uu____6963 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t2  -> FStar_Util.return_all true)), [])
  
let (un_T : tc -> FStar_Syntax_Syntax.term) =
  fun uu___107_6994  ->
    match uu___107_6994 with
    | T (t,uu____6996) -> t
    | uu____7005 -> failwith "Impossible"
  
let (arg_of_tc : tc -> FStar_Syntax_Syntax.arg) =
  fun uu___108_7008  ->
    match uu___108_7008 with
    | T (t,uu____7010) -> FStar_Syntax_Syntax.as_arg t
    | uu____7019 -> failwith "Impossible"
  
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
              | (uu____7135,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r  in
                  let uu____7160 = new_uvar r scope1 k  in
                  (match uu____7160 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____7178 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r
                          in
                       let uu____7195 =
                         let uu____7196 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm"
                            in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____7196
                          in
                       ((T (gi_xs, mk_kind)), uu____7195))
              | (uu____7209,uu____7210,C uu____7211) -> failwith "impos"  in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____7358 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7375;
                         FStar_Syntax_Syntax.vars = uu____7376;_})
                        ->
                        let uu____7399 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____7399 with
                         | (T (gi_xs,uu____7423),prob) ->
                             let uu____7433 =
                               let uu____7434 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____7434
                                in
                             (uu____7433, [prob])
                         | uu____7437 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.pos = uu____7452;
                         FStar_Syntax_Syntax.vars = uu____7453;_})
                        ->
                        let uu____7476 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____7476 with
                         | (T (gi_xs,uu____7500),prob) ->
                             let uu____7510 =
                               let uu____7511 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                                  in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____7511
                                in
                             (uu____7510, [prob])
                         | uu____7514 -> failwith "impossible")
                    | (uu____7525,uu____7526,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.pos = uu____7528;
                         FStar_Syntax_Syntax.vars = uu____7529;_})
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
                        let uu____7660 =
                          let uu____7669 =
                            FStar_List.map (sub_prob scope1 args) components1
                             in
                          FStar_All.pipe_right uu____7669 FStar_List.unzip
                           in
                        (match uu____7660 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____7723 =
                                 let uu____7724 =
                                   let uu____7727 = FStar_List.hd tcs  in
                                   FStar_All.pipe_right uu____7727 un_T  in
                                 let uu____7728 =
                                   let uu____7737 = FStar_List.tl tcs  in
                                   FStar_All.pipe_right uu____7737
                                     (FStar_List.map arg_of_tc)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____7724;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____7728;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 }  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____7723
                                in
                             ((C gi_xs), sub_probs))
                    | uu____7746 ->
                        let uu____7759 = sub_prob scope1 args q  in
                        (match uu____7759 with
                         | (ktec,prob) -> (ktec, [prob]))
                     in
                  (match uu____7358 with
                   | (tc,probs) ->
                       let uu____7790 =
                         match (q, tc) with
                         | ((FStar_Pervasives_Native.Some
                             (b,imp),uu____7853,uu____7854),T
                            (t,uu____7856)) ->
                             let b1 =
                               ((let uu___130_7893 = b  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___130_7893.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___130_7893.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t
                                 }), imp)
                                in
                             let uu____7894 =
                               let uu____7901 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b1
                                  in
                               uu____7901 :: args  in
                             ((FStar_Pervasives_Native.Some b1), (b1 ::
                               scope1), uu____7894)
                         | uu____7936 ->
                             (FStar_Pervasives_Native.None, scope1, args)
                          in
                       (match uu____7790 with
                        | (bopt,scope2,args1) ->
                            let uu____8020 = aux scope2 args1 qs2  in
                            (match uu____8020 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let f1 =
                                         let uu____8058 =
                                           let uu____8061 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           f :: uu____8061  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8058
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
                                         let uu____8086 =
                                           let uu____8089 =
                                             FStar_Syntax_Util.mk_forall u_b
                                               (FStar_Pervasives_Native.fst b)
                                               f
                                              in
                                           let uu____8090 =
                                             FStar_All.pipe_right probs
                                               (FStar_List.map
                                                  (fun prob  ->
                                                     FStar_All.pipe_right
                                                       (p_guard prob)
                                                       FStar_Pervasives_Native.fst))
                                              in
                                           uu____8089 :: uu____8090  in
                                         FStar_Syntax_Util.mk_conj_l
                                           uu____8086
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
  'Auu____8159 .
    worklist ->
      (FStar_Syntax_Syntax.term,'Auu____8159)
        FStar_TypeChecker_Common.problem ->
        (FStar_Syntax_Syntax.term,'Auu____8159)
          FStar_TypeChecker_Common.problem
  =
  fun wl  ->
    fun p  ->
      let uu___131_8180 = p  in
      let uu____8185 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8186 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___131_8180.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8185;
        FStar_TypeChecker_Common.relation =
          (uu___131_8180.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8186;
        FStar_TypeChecker_Common.element =
          (uu___131_8180.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___131_8180.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.scope =
          (uu___131_8180.FStar_TypeChecker_Common.scope);
        FStar_TypeChecker_Common.reason =
          (uu___131_8180.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___131_8180.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___131_8180.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8198 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____8198
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____8207 -> p
  
let (rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____8227 = compress_prob wl pr  in
        FStar_All.pipe_right uu____8227 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8237 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8237 with
           | (lh,uu____8257) ->
               let uu____8278 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8278 with
                | (rh,uu____8298) ->
                    let uu____8319 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8336,FStar_Syntax_Syntax.Tm_uvar uu____8337)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8374,uu____8375)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____8396,FStar_Syntax_Syntax.Tm_uvar uu____8397)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8418,uu____8419)
                          ->
                          let uu____8436 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____8436 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____8485 ->
                                    let rank =
                                      let uu____8493 = is_top_level_prob prob
                                         in
                                      if uu____8493
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____8495 =
                                      let uu___132_8500 = tp  in
                                      let uu____8505 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___132_8500.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___132_8500.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___132_8500.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____8505;
                                        FStar_TypeChecker_Common.element =
                                          (uu___132_8500.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___132_8500.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___132_8500.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___132_8500.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___132_8500.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___132_8500.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____8495)))
                      | (uu____8516,FStar_Syntax_Syntax.Tm_uvar uu____8517)
                          ->
                          let uu____8534 =
                            base_and_refinement wl.tcenv
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____8534 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____8583 ->
                                    let uu____8590 =
                                      let uu___133_8597 = tp  in
                                      let uu____8602 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___133_8597.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____8602;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___133_8597.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___133_8597.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___133_8597.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___133_8597.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___133_8597.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___133_8597.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___133_8597.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___133_8597.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____8590)))
                      | (uu____8619,uu____8620) -> (rigid_rigid, tp)  in
                    (match uu____8319 with
                     | (rank,tp1) ->
                         let uu____8639 =
                           FStar_All.pipe_right
                             (let uu___134_8645 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___134_8645.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___134_8645.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___134_8645.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___134_8645.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___134_8645.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___134_8645.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___134_8645.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___134_8645.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___134_8645.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50)
                            in
                         (rank, uu____8639))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8655 =
            FStar_All.pipe_right
              (let uu___135_8661 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___135_8661.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___135_8661.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___135_8661.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___135_8661.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___135_8661.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___135_8661.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___135_8661.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___135_8661.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___135_8661.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51)
             in
          (rigid_rigid, uu____8655)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun wl  ->
    let rec aux uu____8716 probs =
      match uu____8716 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____8769 = rank wl hd1  in
               (match uu____8769 with
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
    match projectee with | UDeferred _0 -> true | uu____8876 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8888 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8900 -> false
  
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
                        let uu____8940 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8940 with
                        | (k,uu____8946) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8956 -> false)))
            | uu____8957 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9005 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9011 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9011 = (Prims.parse_int "0")))
                           in
                        if uu____9005 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9025 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9031 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9031 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____9025)
               in
            let uu____9032 = filter1 u12  in
            let uu____9035 = filter1 u22  in (uu____9032, uu____9035)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____9058 = filter_out_common_univs us1 us2  in
                (match uu____9058 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____9111 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____9111 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____9114 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____9124 =
                          let uu____9125 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____9126 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____9125
                            uu____9126
                           in
                        UFailed uu____9124))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9146 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9146 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9168 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9168 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____9171 ->
                let uu____9176 =
                  let uu____9177 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____9178 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____9177
                    uu____9178 msg
                   in
                UFailed uu____9176
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9179,uu____9180) ->
              let uu____9181 =
                let uu____9182 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9183 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9182 uu____9183
                 in
              failwith uu____9181
          | (FStar_Syntax_Syntax.U_unknown ,uu____9184) ->
              let uu____9185 =
                let uu____9186 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9187 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9186 uu____9187
                 in
              failwith uu____9185
          | (uu____9188,FStar_Syntax_Syntax.U_bvar uu____9189) ->
              let uu____9190 =
                let uu____9191 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9192 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9191 uu____9192
                 in
              failwith uu____9190
          | (uu____9193,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9194 =
                let uu____9195 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9196 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9195 uu____9196
                 in
              failwith uu____9194
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9220 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____9220
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____9242 = occurs_univ v1 u3  in
              if uu____9242
              then
                let uu____9243 =
                  let uu____9244 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9245 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9244 uu____9245
                   in
                try_umax_components u11 u21 uu____9243
              else
                (let uu____9247 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9247)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____9267 = occurs_univ v1 u3  in
              if uu____9267
              then
                let uu____9268 =
                  let uu____9269 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9270 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9269 uu____9270
                   in
                try_umax_components u11 u21 uu____9268
              else
                (let uu____9272 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9272)
          | (FStar_Syntax_Syntax.U_max uu____9281,uu____9282) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9288 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9288
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9290,FStar_Syntax_Syntax.U_max uu____9291) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9297 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9297
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9299,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9300,FStar_Syntax_Syntax.U_name
             uu____9301) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9302) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9303) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9304,FStar_Syntax_Syntax.U_succ
             uu____9305) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9306,FStar_Syntax_Syntax.U_zero
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
      let uu____9392 = bc1  in
      match uu____9392 with
      | (bs1,mk_cod1) ->
          let uu____9433 = bc2  in
          (match uu____9433 with
           | (bs2,mk_cod2) ->
               let curry n1 bs mk_cod =
                 let uu____9503 = FStar_Util.first_N n1 bs  in
                 match uu____9503 with
                 | (bs3,rest) ->
                     let uu____9528 = mk_cod rest  in (bs3, uu____9528)
                  in
               let l1 = FStar_List.length bs1  in
               let l2 = FStar_List.length bs2  in
               if l1 = l2
               then
                 let uu____9557 =
                   let uu____9564 = mk_cod1 []  in (bs1, uu____9564)  in
                 let uu____9567 =
                   let uu____9574 = mk_cod2 []  in (bs2, uu____9574)  in
                 (uu____9557, uu____9567)
               else
                 if l1 > l2
                 then
                   (let uu____9616 = curry l2 bs1 mk_cod1  in
                    let uu____9629 =
                      let uu____9636 = mk_cod2 []  in (bs2, uu____9636)  in
                    (uu____9616, uu____9629))
                 else
                   (let uu____9652 =
                      let uu____9659 = mk_cod1 []  in (bs1, uu____9659)  in
                    let uu____9662 = curry l1 bs2 mk_cod2  in
                    (uu____9652, uu____9662)))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____9783 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____9783
       then
         let uu____9784 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9784
       else ());
      (let uu____9786 = next_prob probs  in
       match uu____9786 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___136_9807 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___136_9807.wl_deferred);
               ctr = (uu___136_9807.ctr);
               defer_ok = (uu___136_9807.defer_ok);
               smt_ok = (uu___136_9807.smt_ok);
               tcenv = (uu___136_9807.tcenv)
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
                  let uu____9818 = solve_flex_rigid_join env tp probs1  in
                  (match uu____9818 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____9823 = solve_rigid_flex_meet env tp probs1  in
                     match uu____9823 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____9828,uu____9829) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____9846 ->
                let uu____9855 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9914  ->
                          match uu____9914 with
                          | (c,uu____9922,uu____9923) -> c < probs.ctr))
                   in
                (match uu____9855 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9964 =
                            FStar_List.map
                              (fun uu____9979  ->
                                 match uu____9979 with
                                 | (uu____9990,x,y) -> (x, y))
                              probs.wl_deferred
                             in
                          Success uu____9964
                      | uu____9993 ->
                          let uu____10002 =
                            let uu___137_10003 = probs  in
                            let uu____10004 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10025  ->
                                      match uu____10025 with
                                      | (uu____10032,uu____10033,y) -> y))
                               in
                            {
                              attempting = uu____10004;
                              wl_deferred = rest;
                              ctr = (uu___137_10003.ctr);
                              defer_ok = (uu___137_10003.defer_ok);
                              smt_ok = (uu___137_10003.smt_ok);
                              tcenv = (uu___137_10003.tcenv)
                            }  in
                          solve env uu____10002))))

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
            let uu____10040 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10040 with
            | USolved wl1 ->
                let uu____10042 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10042
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
                  let uu____10088 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10088 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10091 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10103;
                  FStar_Syntax_Syntax.vars = uu____10104;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10107;
                  FStar_Syntax_Syntax.vars = uu____10108;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10122,uu____10123) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10130,FStar_Syntax_Syntax.Tm_uinst uu____10131) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10138 -> USolved wl

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
            ((let uu____10148 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10148
              then
                let uu____10149 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10149 msg
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
        (let uu____10158 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____10158
         then
           let uu____10159 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____10159
         else ());
        (let uu____10161 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____10161 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____10223 = head_matches_delta env () t1 t2  in
               match uu____10223 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____10264 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____10313 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10328 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____10329 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____10328, uu____10329)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10334 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____10335 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____10334, uu____10335)
                           in
                        (match uu____10313 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____10361 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____10361
                                in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____10392 =
                                    let uu____10401 =
                                      let uu____10404 =
                                        let uu____10407 =
                                          let uu____10408 =
                                            let uu____10415 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2
                                               in
                                            (x, uu____10415)  in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____10408
                                           in
                                        FStar_Syntax_Syntax.mk uu____10407
                                         in
                                      uu____10404
                                        FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____10423 =
                                      let uu____10426 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort
                                         in
                                      [uu____10426]  in
                                    (uu____10401, uu____10423)  in
                                  FStar_Pervasives_Native.Some uu____10392
                              | (uu____10439,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10441)) ->
                                  let uu____10446 =
                                    let uu____10453 =
                                      let uu____10456 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11
                                         in
                                      [uu____10456]  in
                                    (t11, uu____10453)  in
                                  FStar_Pervasives_Native.Some uu____10446
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____10466),uu____10467) ->
                                  let uu____10472 =
                                    let uu____10479 =
                                      let uu____10482 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21
                                         in
                                      [uu____10482]  in
                                    (t21, uu____10479)  in
                                  FStar_Pervasives_Native.Some uu____10472
                              | uu____10491 ->
                                  let uu____10496 =
                                    FStar_Syntax_Util.head_and_args t11  in
                                  (match uu____10496 with
                                   | (head1,uu____10520) ->
                                       let uu____10541 =
                                         let uu____10542 =
                                           FStar_Syntax_Util.un_uinst head1
                                            in
                                         uu____10542.FStar_Syntax_Syntax.n
                                          in
                                       (match uu____10541 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____10553;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____10555;_}
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
                                        | uu____10562 ->
                                            FStar_Pervasives_Native.None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____10575) ->
                  let uu____10600 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___109_10626  ->
                            match uu___109_10626 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____10633 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____10633 with
                                      | (u',uu____10649) ->
                                          let uu____10670 =
                                            let uu____10671 = whnf env u'  in
                                            uu____10671.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____10670 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____10675) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____10700 -> false))
                                 | uu____10701 -> false)
                            | uu____10704 -> false))
                     in
                  (match uu____10600 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____10738 tps =
                         match uu____10738 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____10786 =
                                    let uu____10795 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound uu____10795  in
                                  (match uu____10786 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____10830 -> FStar_Pervasives_Native.None)
                          in
                       let uu____10839 =
                         let uu____10848 =
                           let uu____10855 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (uu____10855, [])  in
                         make_lower_bound uu____10848 lower_bounds  in
                       (match uu____10839 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____10867 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____10867
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
                            ((let uu____10887 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____10887
                              then
                                let wl' =
                                  let uu___138_10889 = wl  in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred =
                                      (uu___138_10889.wl_deferred);
                                    ctr = (uu___138_10889.ctr);
                                    defer_ok = (uu___138_10889.defer_ok);
                                    smt_ok = (uu___138_10889.smt_ok);
                                    tcenv = (uu___138_10889.tcenv)
                                  }  in
                                let uu____10890 = wl_to_string wl'  in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____10890
                              else ());
                             (let uu____10892 =
                                solve_t env eq_prob
                                  (let uu___139_10894 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___139_10894.wl_deferred);
                                     ctr = (uu___139_10894.ctr);
                                     defer_ok = (uu___139_10894.defer_ok);
                                     smt_ok = (uu___139_10894.smt_ok);
                                     tcenv = (uu___139_10894.tcenv)
                                   })
                                 in
                              match uu____10892 with
                              | Success uu____10897 ->
                                  let wl1 =
                                    let uu___140_10899 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___140_10899.wl_deferred);
                                      ctr = (uu___140_10899.ctr);
                                      defer_ok = (uu___140_10899.defer_ok);
                                      smt_ok = (uu___140_10899.smt_ok);
                                      tcenv = (uu___140_10899.tcenv)
                                    }  in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1
                                     in
                                  let uu____10901 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds
                                     in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____10906 -> FStar_Pervasives_Native.None))))
              | uu____10907 -> failwith "Impossible: Not a rigid-flex"))

and (solve_flex_rigid_join :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____10916 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____10916
         then
           let uu____10917 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____10917
         else ());
        (let uu____10919 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____10919 with
         | (u,args) ->
             let uu____10958 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____10958 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i  in
                  let base_types_match t1 t2 =
                    let uu____10999 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____10999 with
                    | (h1,args1) ->
                        let uu____11040 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____11040 with
                         | (h2,uu____11060) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____11087 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  if uu____11087
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____11105 =
                                          let uu____11108 =
                                            let uu____11109 =
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
                                                   _0_53) uu____11109
                                             in
                                          [uu____11108]  in
                                        FStar_Pervasives_Native.Some
                                          uu____11105))
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
                                       (let uu____11142 =
                                          let uu____11145 =
                                            let uu____11146 =
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
                                                   _0_54) uu____11146
                                             in
                                          [uu____11145]  in
                                        FStar_Pervasives_Native.Some
                                          uu____11142))
                                  else FStar_Pervasives_Native.None
                              | uu____11160 -> FStar_Pervasives_Native.None))
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
                             let uu____11250 =
                               let uu____11259 =
                                 let uu____11262 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21  in
                                 FStar_Syntax_Util.refine x1 uu____11262  in
                               (uu____11259, m1)  in
                             FStar_Pervasives_Native.Some uu____11250)
                    | (uu____11275,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____11277)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____11325),uu____11326) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____11373 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____11426) ->
                       let uu____11451 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___110_11477  ->
                                 match uu___110_11477 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____11484 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____11484 with
                                           | (u',uu____11500) ->
                                               let uu____11521 =
                                                 let uu____11522 =
                                                   whnf env u'  in
                                                 uu____11522.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____11521 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____11526) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____11551 -> false))
                                      | uu____11552 -> false)
                                 | uu____11555 -> false))
                          in
                       (match uu____11451 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____11593 tps =
                              match uu____11593 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____11655 =
                                         let uu____11666 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound uu____11666  in
                                       (match uu____11655 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____11717 ->
                                       FStar_Pervasives_Native.None)
                               in
                            let uu____11728 =
                              let uu____11739 =
                                let uu____11748 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (uu____11748, [])  in
                              make_upper_bound uu____11739 upper_bounds  in
                            (match uu____11728 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____11762 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____11762
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
                                 ((let uu____11788 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____11788
                                   then
                                     let wl' =
                                       let uu___141_11790 = wl  in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___141_11790.wl_deferred);
                                         ctr = (uu___141_11790.ctr);
                                         defer_ok = (uu___141_11790.defer_ok);
                                         smt_ok = (uu___141_11790.smt_ok);
                                         tcenv = (uu___141_11790.tcenv)
                                       }  in
                                     let uu____11791 = wl_to_string wl'  in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____11791
                                   else ());
                                  (let uu____11793 =
                                     solve_t env eq_prob
                                       (let uu___142_11795 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___142_11795.wl_deferred);
                                          ctr = (uu___142_11795.ctr);
                                          defer_ok =
                                            (uu___142_11795.defer_ok);
                                          smt_ok = (uu___142_11795.smt_ok);
                                          tcenv = (uu___142_11795.tcenv)
                                        })
                                      in
                                   match uu____11793 with
                                   | Success uu____11798 ->
                                       let wl1 =
                                         let uu___143_11800 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___143_11800.wl_deferred);
                                           ctr = (uu___143_11800.ctr);
                                           defer_ok =
                                             (uu___143_11800.defer_ok);
                                           smt_ok = (uu___143_11800.smt_ok);
                                           tcenv = (uu___143_11800.tcenv)
                                         }  in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1
                                          in
                                       let uu____11802 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds
                                          in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____11807 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____11808 -> failwith "Impossible: Not a flex-rigid")))

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
                    ((let uu____11883 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____11883
                      then
                        let uu____11884 = prob_to_string env1 rhs_prob  in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____11884
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst
                         in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___144_11938 = hd1  in
                      let uu____11939 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___144_11938.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___144_11938.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11939
                      }  in
                    let hd21 =
                      let uu___145_11943 = hd2  in
                      let uu____11944 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___145_11943.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___145_11943.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____11944
                      }  in
                    let prob =
                      let uu____11948 =
                        let uu____11953 =
                          FStar_All.pipe_left invert_rel (p_rel orig)  in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____11953 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter"
                         in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____11948
                       in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                    let subst2 =
                      let uu____11964 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1
                         in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____11964
                       in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                    let uu____11968 =
                      aux (FStar_List.append scope [(hd12, imp)]) env2 subst2
                        xs1 ys1
                       in
                    (match uu____11968 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____12006 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst
                              in
                           let uu____12011 =
                             close_forall env2 [(hd12, imp)] phi  in
                           FStar_Syntax_Util.mk_conj uu____12006 uu____12011
                            in
                         ((let uu____12021 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____12021
                           then
                             let uu____12022 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____12023 =
                               FStar_Syntax_Print.bv_to_string hd12  in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____12022 uu____12023
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail1 -> fail1)
                | uu____12046 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch"
                 in
              let scope = p_scope orig  in
              let uu____12056 = aux scope env [] bs1 bs2  in
              match uu____12056 with
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
        let uu____12080 = compress_tprob wl problem  in
        solve_t' env uu____12080 wl

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____12113 = head_matches_delta env1 wl1 t1 t2  in
          match uu____12113 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____12144,uu____12145) ->
                   let rec may_relate head3 =
                     let uu____12170 =
                       let uu____12171 = FStar_Syntax_Subst.compress head3
                          in
                       uu____12171.FStar_Syntax_Syntax.n  in
                     match uu____12170 with
                     | FStar_Syntax_Syntax.Tm_name uu____12174 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____12175 -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____12198;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_equational ;
                           FStar_Syntax_Syntax.fv_qual = uu____12199;_}
                         -> true
                     | FStar_Syntax_Syntax.Tm_fvar
                         { FStar_Syntax_Syntax.fv_name = uu____12202;
                           FStar_Syntax_Syntax.fv_delta =
                             FStar_Syntax_Syntax.Delta_abstract uu____12203;
                           FStar_Syntax_Syntax.fv_qual = uu____12204;_}
                         ->
                         problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____12208,uu____12209) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____12251) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____12257) ->
                         may_relate t
                     | uu____12262 -> false  in
                   let uu____12263 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok
                      in
                   if uu____12263
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
                                let uu____12280 =
                                  let uu____12281 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____12281 t21
                                   in
                                FStar_Syntax_Util.mk_forall u_x x uu____12280
                             in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1)
                        in
                     let uu____12283 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1
                        in
                     solve env1 uu____12283
                   else
                     (let uu____12285 =
                        let uu____12286 =
                          FStar_Syntax_Print.term_to_string head1  in
                        let uu____12287 =
                          FStar_Syntax_Print.term_to_string head2  in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____12286 uu____12287
                         in
                      giveup env1 uu____12285 orig)
               | (uu____12288,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___146_12302 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___146_12302.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___146_12302.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___146_12302.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___146_12302.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___146_12302.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___146_12302.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___146_12302.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___146_12302.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____12303,FStar_Pervasives_Native.None ) ->
                   ((let uu____12315 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____12315
                     then
                       let uu____12316 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12317 = FStar_Syntax_Print.tag_of_term t1
                          in
                       let uu____12318 = FStar_Syntax_Print.term_to_string t2
                          in
                       let uu____12319 = FStar_Syntax_Print.tag_of_term t2
                          in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____12316
                         uu____12317 uu____12318 uu____12319
                     else ());
                    (let uu____12321 = FStar_Syntax_Util.head_and_args t1  in
                     match uu____12321 with
                     | (head11,args1) ->
                         let uu____12358 = FStar_Syntax_Util.head_and_args t2
                            in
                         (match uu____12358 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1  in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____12412 =
                                  let uu____12413 =
                                    FStar_Syntax_Print.term_to_string head11
                                     in
                                  let uu____12414 = args_to_string args1  in
                                  let uu____12415 =
                                    FStar_Syntax_Print.term_to_string head21
                                     in
                                  let uu____12416 = args_to_string args2  in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____12413 uu____12414 uu____12415
                                    uu____12416
                                   in
                                giveup env1 uu____12412 orig
                              else
                                (let uu____12418 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____12424 =
                                        FStar_Syntax_Util.eq_args args1 args2
                                         in
                                      uu____12424 = FStar_Syntax_Util.Equal)
                                    in
                                 if uu____12418
                                 then
                                   let uu____12425 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1
                                      in
                                   match uu____12425 with
                                   | USolved wl2 ->
                                       let uu____12427 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2
                                          in
                                       solve env1 uu____12427
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____12431 =
                                      base_and_refinement env1 t1  in
                                    match uu____12431 with
                                    | (base1,refinement1) ->
                                        let uu____12456 =
                                          base_and_refinement env1 t2  in
                                        (match uu____12456 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____12513 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1
                                                     in
                                                  (match uu____12513 with
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
                                                           (fun uu____12535 
                                                              ->
                                                              fun uu____12536
                                                                 ->
                                                                match 
                                                                  (uu____12535,
                                                                    uu____12536)
                                                                with
                                                                | ((a,uu____12554),
                                                                   (a',uu____12556))
                                                                    ->
                                                                    let uu____12565
                                                                    =
                                                                    let uu____12570
                                                                    =
                                                                    p_scope
                                                                    orig  in
                                                                    mk_problem
                                                                    uu____12570
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
                                                                    uu____12565)
                                                           args1 args2
                                                          in
                                                       let formula =
                                                         let uu____12576 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____12576
                                                          in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2
                                                          in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____12582 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1)
                                                     in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2)
                                                     in
                                                  solve_t env1
                                                    (let uu___147_12618 =
                                                       problem  in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___147_12618.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___147_12618.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___147_12618.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___147_12618.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___147_12618.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___147_12618.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___147_12618.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___147_12618.FStar_TypeChecker_Common.rank)
                                                     }) wl1))))))))
           in
        let force_quasi_pattern xs_opt uu____12651 =
          match uu____12651 with
          | (t,u,k,args) ->
              let debug1 f =
                let uu____12693 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12693 then f () else ()  in
              let rec aux pat_args pat_args_set pattern_vars pattern_var_set
                seen_formals formals res_t args1 =
                debug1
                  (fun uu____12789  ->
                     let uu____12790 =
                       FStar_Syntax_Print.binders_to_string ", " pat_args  in
                     FStar_Util.print1 "pat_args so far: {%s}\n" uu____12790);
                (match (formals, args1) with
                 | ([],[]) ->
                     let pat_args1 =
                       FStar_All.pipe_right (FStar_List.rev pat_args)
                         (FStar_List.map
                            (fun uu____12858  ->
                               match uu____12858 with
                               | (x,imp) ->
                                   let uu____12869 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   (uu____12869, imp)))
                        in
                     let pattern_vars1 = FStar_List.rev pattern_vars  in
                     let kk =
                       let uu____12882 = FStar_Syntax_Util.type_u ()  in
                       match uu____12882 with
                       | (t1,uu____12888) ->
                           let uu____12889 =
                             new_uvar t1.FStar_Syntax_Syntax.pos
                               pattern_vars1 t1
                              in
                           FStar_Pervasives_Native.fst uu____12889
                        in
                     let uu____12894 =
                       new_uvar t.FStar_Syntax_Syntax.pos pattern_vars1 kk
                        in
                     (match uu____12894 with
                      | (t',tm_u1) ->
                          let uu____12907 = destruct_flex_t t'  in
                          (match uu____12907 with
                           | (uu____12944,u1,k1,uu____12947) ->
                               let all_formals = FStar_List.rev seen_formals
                                  in
                               let k2 =
                                 let uu____13006 =
                                   FStar_Syntax_Syntax.mk_Total res_t  in
                                 FStar_Syntax_Util.arrow all_formals
                                   uu____13006
                                  in
                               let sol =
                                 let uu____13010 =
                                   let uu____13019 = u_abs k2 all_formals t'
                                      in
                                   ((u, k2), uu____13019)  in
                                 TERM uu____13010  in
                               let t_app =
                                 FStar_Syntax_Syntax.mk_Tm_app tm_u1
                                   pat_args1 FStar_Pervasives_Native.None
                                   t.FStar_Syntax_Syntax.pos
                                  in
                               FStar_Pervasives_Native.Some
                                 (sol, (t_app, u1, k1, pat_args1))))
                 | (formal::formals1,hd1::tl1) ->
                     (debug1
                        (fun uu____13154  ->
                           let uu____13155 =
                             FStar_Syntax_Print.binder_to_string formal  in
                           let uu____13156 =
                             FStar_Syntax_Print.args_to_string [hd1]  in
                           FStar_Util.print2
                             "force_quasi_pattern (case 2): formal=%s, hd=%s\n"
                             uu____13155 uu____13156);
                      (let uu____13169 = pat_var_opt env pat_args hd1  in
                       match uu____13169 with
                       | FStar_Pervasives_Native.None  ->
                           (debug1
                              (fun uu____13189  ->
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
                                      (fun uu____13232  ->
                                         match uu____13232 with
                                         | (x,uu____13238) ->
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
                                (fun uu____13253  ->
                                   let uu____13254 =
                                     FStar_Syntax_Print.args_to_string [hd1]
                                      in
                                   let uu____13267 =
                                     FStar_Syntax_Print.binder_to_string y
                                      in
                                   FStar_Util.print2
                                     "%s (var = %s) maybe pat\n" uu____13254
                                     uu____13267);
                              (let fvs =
                                 FStar_Syntax_Free.names
                                   (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort
                                  in
                               let uu____13271 =
                                 let uu____13272 =
                                   FStar_Util.set_is_subset_of fvs
                                     pat_args_set
                                    in
                                 Prims.op_Negation uu____13272  in
                               if uu____13271
                               then
                                 (debug1
                                    (fun uu____13284  ->
                                       let uu____13285 =
                                         let uu____13288 =
                                           FStar_Syntax_Print.args_to_string
                                             [hd1]
                                            in
                                         let uu____13301 =
                                           let uu____13304 =
                                             FStar_Syntax_Print.binder_to_string
                                               y
                                              in
                                           let uu____13305 =
                                             let uu____13308 =
                                               FStar_Syntax_Print.term_to_string
                                                 (FStar_Pervasives_Native.fst
                                                    y).FStar_Syntax_Syntax.sort
                                                in
                                             let uu____13309 =
                                               let uu____13312 =
                                                 names_to_string fvs  in
                                               let uu____13313 =
                                                 let uu____13316 =
                                                   names_to_string
                                                     pattern_var_set
                                                    in
                                                 [uu____13316]  in
                                               uu____13312 :: uu____13313  in
                                             uu____13308 :: uu____13309  in
                                           uu____13304 :: uu____13305  in
                                         uu____13288 :: uu____13301  in
                                       FStar_Util.print
                                         "BUT! %s (var = %s) is not a pat because its type %s contains {%s} fvs which are not included in the pattern vars so far {%s}\n"
                                         uu____13285);
                                  aux pat_args pat_args_set pattern_vars
                                    pattern_var_set (formal :: seen_formals)
                                    formals1 res_t tl1)
                               else
                                 (let uu____13318 =
                                    FStar_Util.set_add
                                      (FStar_Pervasives_Native.fst y)
                                      pat_args_set
                                     in
                                  let uu____13321 =
                                    FStar_Util.set_add
                                      (FStar_Pervasives_Native.fst formal)
                                      pattern_var_set
                                     in
                                  aux (y :: pat_args) uu____13318 (formal ::
                                    pattern_vars) uu____13321 (formal ::
                                    seen_formals) formals1 res_t tl1)))))
                 | ([],uu____13328::uu____13329) ->
                     let uu____13360 =
                       let uu____13373 =
                         FStar_TypeChecker_Normalize.unfold_whnf env res_t
                          in
                       FStar_Syntax_Util.arrow_formals uu____13373  in
                     (match uu____13360 with
                      | (more_formals,res_t1) ->
                          (match more_formals with
                           | [] -> FStar_Pervasives_Native.None
                           | uu____13412 ->
                               aux pat_args pat_args_set pattern_vars
                                 pattern_var_set seen_formals more_formals
                                 res_t1 args1))
                 | (uu____13419::uu____13420,[]) ->
                     FStar_Pervasives_Native.None)
                 in
              let uu____13443 =
                let uu____13456 =
                  FStar_TypeChecker_Normalize.unfold_whnf env k  in
                FStar_Syntax_Util.arrow_formals uu____13456  in
              (match uu____13443 with
               | (all_formals,res_t) ->
                   (debug1
                      (fun uu____13492  ->
                         let uu____13493 =
                           FStar_Syntax_Print.term_to_string t  in
                         let uu____13494 =
                           FStar_Syntax_Print.binders_to_string ", "
                             all_formals
                            in
                         let uu____13495 =
                           FStar_Syntax_Print.term_to_string res_t  in
                         let uu____13496 =
                           FStar_Syntax_Print.args_to_string args  in
                         FStar_Util.print4
                           "force_quasi_pattern of %s with all_formals={%s}, res_t={%s} and args={%s}\n"
                           uu____13493 uu____13494 uu____13495 uu____13496);
                    (let uu____13497 = FStar_Syntax_Syntax.new_bv_set ()  in
                     let uu____13500 = FStar_Syntax_Syntax.new_bv_set ()  in
                     aux [] uu____13497 [] uu____13500 [] all_formals res_t
                       args)))
           in
        let use_pattern_equality orig env1 wl1 lhs pat_vars1 rhs =
          let uu____13534 = lhs  in
          match uu____13534 with
          | (t1,uv,k_uv,args_lhs) ->
              let sol =
                match pat_vars1 with
                | [] -> rhs
                | uu____13544 ->
                    let uu____13545 = sn_binders env1 pat_vars1  in
                    u_abs k_uv uu____13545 rhs
                 in
              let wl2 =
                solve_prob orig FStar_Pervasives_Native.None
                  [TERM ((uv, k_uv), sol)] wl1
                 in
              solve env1 wl2
           in
        let imitate orig env1 wl1 p =
          let uu____13568 = p  in
          match uu____13568 with
          | (((u,k),xs,c),ps,(h,uu____13579,qs)) ->
              let xs1 = sn_binders env1 xs  in
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____13661 = imitation_sub_probs orig env1 xs1 ps qs  in
              (match uu____13661 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____13684 = h gs_xs  in
                     let uu____13685 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> FStar_Pervasives_Native.Some _0_57)
                        in
                     FStar_Syntax_Util.abs xs1 uu____13684 uu____13685  in
                   ((let uu____13691 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____13691
                     then
                       let uu____13692 =
                         let uu____13695 =
                           let uu____13696 =
                             FStar_List.map tc_to_string gs_xs  in
                           FStar_All.pipe_right uu____13696
                             (FStar_String.concat "\n\t>")
                            in
                         let uu____13701 =
                           let uu____13704 =
                             FStar_Syntax_Print.binders_to_string ", " xs1
                              in
                           let uu____13705 =
                             let uu____13708 =
                               FStar_Syntax_Print.comp_to_string c  in
                             let uu____13709 =
                               let uu____13712 =
                                 FStar_Syntax_Print.term_to_string im  in
                               let uu____13713 =
                                 let uu____13716 =
                                   FStar_Syntax_Print.tag_of_term im  in
                                 let uu____13717 =
                                   let uu____13720 =
                                     let uu____13721 =
                                       FStar_List.map (prob_to_string env1)
                                         sub_probs
                                        in
                                     FStar_All.pipe_right uu____13721
                                       (FStar_String.concat ", ")
                                      in
                                   let uu____13726 =
                                     let uu____13729 =
                                       FStar_TypeChecker_Normalize.term_to_string
                                         env1 formula
                                        in
                                     [uu____13729]  in
                                   uu____13720 :: uu____13726  in
                                 uu____13716 :: uu____13717  in
                               uu____13712 :: uu____13713  in
                             uu____13708 :: uu____13709  in
                           uu____13704 :: uu____13705  in
                         uu____13695 :: uu____13701  in
                       FStar_Util.print
                         "Imitating gs_xs=\n\t>%s\n\t binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____13692
                     else ());
                    def_check_closed (p_loc orig) "imitate" im;
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1
                        in
                     solve env1 (attempt sub_probs wl2))))
           in
        let imitate' orig env1 wl1 uu___111_13751 =
          match uu___111_13751 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p  in
        let project orig env1 wl1 i p =
          let uu____13783 = p  in
          match uu____13783 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____13874 = FStar_List.nth ps i  in
              (match uu____13874 with
               | (pi,uu____13878) ->
                   let uu____13883 = FStar_List.nth xs i  in
                   (match uu____13883 with
                    | (xi,uu____13895) ->
                        let rec gs k =
                          let uu____13908 =
                            let uu____13921 =
                              FStar_TypeChecker_Normalize.unfold_whnf env1 k
                               in
                            FStar_Syntax_Util.arrow_formals uu____13921  in
                          match uu____13908 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____13996)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort
                                       in
                                    let uu____14009 = new_uvar r xs k_a  in
                                    (match uu____14009 with
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
                                         let uu____14031 = aux subst2 tl1  in
                                         (match uu____14031 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____14058 =
                                                let uu____14061 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1
                                                   in
                                                uu____14061 :: gi_xs'  in
                                              let uu____14062 =
                                                let uu____14065 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps
                                                   in
                                                uu____14065 :: gi_ps'  in
                                              (uu____14058, uu____14062)))
                                 in
                              aux [] bs
                           in
                        let uu____14070 =
                          let uu____14071 = matches pi  in
                          FStar_All.pipe_left Prims.op_Negation uu____14071
                           in
                        if uu____14070
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____14075 = gs xi.FStar_Syntax_Syntax.sort
                              in
                           match uu____14075 with
                           | (g_xs,uu____14087) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                  in
                               let proj =
                                 let uu____14098 =
                                   FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs
                                     FStar_Pervasives_Native.None r
                                    in
                                 let uu____14099 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c)
                                     (fun _0_58  ->
                                        FStar_Pervasives_Native.Some _0_58)
                                    in
                                 FStar_Syntax_Util.abs xs uu____14098
                                   uu____14099
                                  in
                               let sub1 =
                                 let uu____14105 =
                                   let uu____14110 = p_scope orig  in
                                   let uu____14111 =
                                     FStar_Syntax_Syntax.mk_Tm_app proj ps
                                       FStar_Pervasives_Native.None r
                                      in
                                   let uu____14114 =
                                     let uu____14117 =
                                       FStar_List.map
                                         (fun uu____14132  ->
                                            match uu____14132 with
                                            | (uu____14141,uu____14142,y) ->
                                                y) qs
                                        in
                                     FStar_All.pipe_left h uu____14117  in
                                   mk_problem uu____14110 orig uu____14111
                                     (p_rel orig) uu____14114
                                     FStar_Pervasives_Native.None
                                     "projection"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____14105
                                  in
                               ((let uu____14157 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____14157
                                 then
                                   let uu____14158 =
                                     FStar_Syntax_Print.term_to_string proj
                                      in
                                   let uu____14159 = prob_to_string env1 sub1
                                      in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____14158 uu____14159
                                 else ());
                                (let wl2 =
                                   let uu____14162 =
                                     let uu____14165 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1)
                                        in
                                     FStar_Pervasives_Native.Some uu____14165
                                      in
                                   solve_prob orig uu____14162
                                     [TERM (u, proj)] wl1
                                    in
                                 let uu____14174 =
                                   solve env1 (attempt [sub1] wl2)  in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_Pervasives_Native.Some _0_60)
                                   uu____14174)))))
           in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____14205 = lhs  in
          match uu____14205 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____14241 = FStar_Syntax_Util.arrow_formals_comp k_uv
                   in
                match uu____14241 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____14274 =
                        let uu____14321 = decompose env t2  in
                        (((uv, k_uv), xs, c), ps, uu____14321)  in
                      FStar_Pervasives_Native.Some uu____14274
                    else
                      (let rec elim k args =
                         let k1 =
                           FStar_TypeChecker_Normalize.unfold_whnf env k  in
                         let uu____14465 =
                           let uu____14472 =
                             let uu____14473 = FStar_Syntax_Subst.compress k1
                                in
                             uu____14473.FStar_Syntax_Syntax.n  in
                           (uu____14472, args)  in
                         match uu____14465 with
                         | (uu____14484,[]) ->
                             let uu____14487 =
                               let uu____14498 =
                                 FStar_Syntax_Syntax.mk_Total k1  in
                               ([], uu____14498)  in
                             FStar_Pervasives_Native.Some uu____14487
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____14519,uu____14520) ->
                             let uu____14541 =
                               FStar_Syntax_Util.head_and_args k1  in
                             (match uu____14541 with
                              | (uv1,uv_args) ->
                                  let uu____14584 =
                                    let uu____14585 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____14585.FStar_Syntax_Syntax.n  in
                                  (match uu____14584 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14595) ->
                                       let uu____14620 =
                                         pat_vars env [] uv_args  in
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
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____14656
                                                                FStar_Pervasives_Native.fst
                                                               in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14655
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14650
                                                           in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14649
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14648))
                                               in
                                            let c1 =
                                              let uu____14666 =
                                                let uu____14667 =
                                                  let uu____14672 =
                                                    let uu____14673 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____14673
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14672
                                                   in
                                                FStar_Pervasives_Native.fst
                                                  uu____14667
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14666
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____14686 =
                                                let uu____14689 =
                                                  let uu____14690 =
                                                    let uu____14693 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____14693
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14690
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____14689
                                                 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14686
                                               in
                                            (def_check_closed (p_loc orig)
                                               "solve_t_flex_rigid.subterms"
                                               uv_sol;
                                             FStar_Syntax_Util.set_uvar uvar
                                               uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14712 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app
                            uu____14717,uu____14718) ->
                             let uu____14737 =
                               FStar_Syntax_Util.head_and_args k1  in
                             (match uu____14737 with
                              | (uv1,uv_args) ->
                                  let uu____14780 =
                                    let uu____14781 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____14781.FStar_Syntax_Syntax.n  in
                                  (match uu____14780 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____14791) ->
                                       let uu____14816 =
                                         pat_vars env [] uv_args  in
                                       (match uu____14816 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____14843  ->
                                                      let uu____14844 =
                                                        let uu____14845 =
                                                          let uu____14846 =
                                                            let uu____14851 =
                                                              let uu____14852
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____14852
                                                                FStar_Pervasives_Native.fst
                                                               in
                                                            new_uvar
                                                              k1.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____14851
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____14846
                                                           in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k1.FStar_Syntax_Syntax.pos))
                                                          uu____14845
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____14844))
                                               in
                                            let c1 =
                                              let uu____14862 =
                                                let uu____14863 =
                                                  let uu____14868 =
                                                    let uu____14869 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____14869
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  new_uvar
                                                    k1.FStar_Syntax_Syntax.pos
                                                    scope uu____14868
                                                   in
                                                FStar_Pervasives_Native.fst
                                                  uu____14863
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____14862
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____14882 =
                                                let uu____14885 =
                                                  let uu____14886 =
                                                    let uu____14889 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____14889
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____14886
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____14885
                                                 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____14882
                                               in
                                            (def_check_closed (p_loc orig)
                                               "solve_t_flex_rigid.subterms"
                                               uv_sol;
                                             FStar_Syntax_Util.set_uvar uvar
                                               uv_sol;
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____14908 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow
                            (xs1,c1),uu____14915) ->
                             let n_args = FStar_List.length args  in
                             let n_xs = FStar_List.length xs1  in
                             if n_xs = n_args
                             then
                               let uu____14956 =
                                 FStar_Syntax_Subst.open_comp xs1 c1  in
                               FStar_All.pipe_right uu____14956
                                 (fun _0_61  ->
                                    FStar_Pervasives_Native.Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____14992 =
                                    FStar_Util.first_N n_xs args  in
                                  match uu____14992 with
                                  | (args1,rest) ->
                                      let uu____15021 =
                                        FStar_Syntax_Subst.open_comp xs1 c1
                                         in
                                      (match uu____15021 with
                                       | (xs2,c2) ->
                                           let uu____15034 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest
                                              in
                                           FStar_Util.bind_opt uu____15034
                                             (fun uu____15058  ->
                                                match uu____15058 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____15098 =
                                    FStar_Util.first_N n_args xs1  in
                                  match uu____15098 with
                                  | (xs2,rest) ->
                                      let t =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_arrow
                                             (rest, c1))
                                          FStar_Pervasives_Native.None
                                          k1.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____15166 =
                                        let uu____15171 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____15171
                                         in
                                      FStar_All.pipe_right uu____15166
                                        (fun _0_62  ->
                                           FStar_Pervasives_Native.Some _0_62))
                         | uu____15186 ->
                             let uu____15193 =
                               let uu____15198 =
                                 let uu____15199 =
                                   FStar_Syntax_Print.uvar_to_string uv  in
                                 let uu____15200 =
                                   FStar_Syntax_Print.term_to_string k1  in
                                 let uu____15201 =
                                   FStar_Syntax_Print.term_to_string k_uv  in
                                 FStar_Util.format3
                                   "Impossible: ill-typed application %s : %s\n\t%s"
                                   uu____15199 uu____15200 uu____15201
                                  in
                               (FStar_Errors.Fatal_IllTyped, uu____15198)  in
                             FStar_Errors.raise_error uu____15193
                               t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15208 = elim k_uv ps  in
                       FStar_Util.bind_opt uu____15208
                         (fun uu____15263  ->
                            match uu____15263 with
                            | (xs1,c1) ->
                                let uu____15312 =
                                  let uu____15353 = decompose env t2  in
                                  (((uv, k_uv), xs1, c1), ps, uu____15353)
                                   in
                                FStar_Pervasives_Native.Some uu____15312))
                 in
              let imitate_or_project n1 lhs1 rhs stopt =
                let fail1 uu____15474 =
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig
                   in
                let rec try_project st i =
                  if i >= n1
                  then fail1 ()
                  else
                    (let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                     let uu____15488 = project orig env wl1 i st  in
                     match uu____15488 with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some (Failed uu____15502) ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          try_project st (i + (Prims.parse_int "1")))
                     | FStar_Pervasives_Native.Some sol -> sol)
                   in
                if FStar_Option.isSome stopt
                then
                  let st = FStar_Util.must stopt  in
                  let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                  let uu____15517 = imitate orig env wl1 st  in
                  match uu____15517 with
                  | Failed uu____15522 ->
                      (FStar_Syntax_Unionfind.rollback tx;
                       try_project st (Prims.parse_int "0"))
                  | sol -> sol
                else fail1 ()  in
              let pattern_eq_imitate_or_project n1 lhs1 rhs stopt =
                let uu____15553 =
                  force_quasi_pattern FStar_Pervasives_Native.None lhs1  in
                match uu____15553 with
                | FStar_Pervasives_Native.None  ->
                    imitate_or_project n1 lhs1 rhs stopt
                | FStar_Pervasives_Native.Some (sol,forced_lhs_pattern) ->
                    let uu____15576 = forced_lhs_pattern  in
                    (match uu____15576 with
                     | (lhs_t,uu____15578,uu____15579,uu____15580) ->
                         ((let uu____15582 =
                             FStar_TypeChecker_Env.debug env
                               (FStar_Options.Other "Rel")
                              in
                           if uu____15582
                           then
                             let uu____15583 = lhs1  in
                             match uu____15583 with
                             | (t0,uu____15585,uu____15586,uu____15587) ->
                                 let uu____15588 = forced_lhs_pattern  in
                                 (match uu____15588 with
                                  | (t11,uu____15590,uu____15591,uu____15592)
                                      ->
                                      let uu____15593 =
                                        FStar_Syntax_Print.term_to_string t0
                                         in
                                      let uu____15594 =
                                        FStar_Syntax_Print.term_to_string t11
                                         in
                                      FStar_Util.print2
                                        "force_quasi_pattern succeeded, turning %s into %s\n"
                                        uu____15593 uu____15594)
                           else ());
                          (let rhs_vars = FStar_Syntax_Free.names rhs  in
                           let lhs_vars = FStar_Syntax_Free.names lhs_t  in
                           let uu____15602 =
                             FStar_Util.set_is_subset_of rhs_vars lhs_vars
                              in
                           if uu____15602
                           then
                             ((let uu____15604 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "Rel")
                                  in
                               if uu____15604
                               then
                                 let uu____15605 =
                                   FStar_Syntax_Print.term_to_string rhs  in
                                 let uu____15606 = names_to_string rhs_vars
                                    in
                                 let uu____15607 = names_to_string lhs_vars
                                    in
                                 FStar_Util.print3
                                   "fvar check succeeded for quasi pattern ...\n\trhs = %s, rhs_vars=%s\nlhs_vars=%s ... proceeding\n"
                                   uu____15605 uu____15606 uu____15607
                               else ());
                              (let tx =
                                 FStar_Syntax_Unionfind.new_transaction ()
                                  in
                               let wl2 =
                                 extend_solution (p_pid orig) [sol] wl1  in
                               let uu____15611 =
                                 let uu____15612 =
                                   FStar_TypeChecker_Common.as_tprob orig  in
                                 solve_t env uu____15612 wl2  in
                               match uu____15611 with
                               | Failed uu____15613 ->
                                   (FStar_Syntax_Unionfind.rollback tx;
                                    imitate_or_project n1 lhs1 rhs stopt)
                               | sol1 -> sol1))
                           else
                             ((let uu____15622 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "Rel")
                                  in
                               if uu____15622
                               then
                                 FStar_Util.print_string
                                   "fvar check failed for quasi pattern ... im/proj\n"
                               else ());
                              imitate_or_project n1 lhs1 rhs stopt))))
                 in
              let check_head fvs1 t21 =
                let uu____15635 = FStar_Syntax_Util.head_and_args t21  in
                match uu____15635 with
                | (hd1,uu____15651) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15672 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____15685 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____15686 -> true
                     | uu____15703 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1  in
                         let uu____15707 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1  in
                         if uu____15707
                         then true
                         else
                           ((let uu____15710 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____15710
                             then
                               let uu____15711 = names_to_string fvs_hd  in
                               FStar_Util.print1 "Free variables are %s\n"
                                 uu____15711
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
                   let uu____15731 = occurs_check env wl1 (uv, k_uv) t21  in
                   (match uu____15731 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____15744 =
                            let uu____15745 = FStar_Option.get msg  in
                            Prims.strcat "occurs-check failed: " uu____15745
                             in
                          giveup_or_defer1 orig uu____15744
                        else
                          (let uu____15747 =
                             FStar_Util.set_is_subset_of fvs2 fvs1  in
                           if uu____15747
                           then
                             let uu____15748 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
                                in
                             (if uu____15748
                              then
                                let uu____15749 = subterms args_lhs  in
                                imitate' orig env wl1 uu____15749
                              else
                                ((let uu____15754 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____15754
                                  then
                                    let uu____15755 =
                                      FStar_Syntax_Print.term_to_string t11
                                       in
                                    let uu____15756 = names_to_string fvs1
                                       in
                                    let uu____15757 = names_to_string fvs2
                                       in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____15755 uu____15756 uu____15757
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
                               (let uu____15761 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21)
                                   in
                                if uu____15761
                                then
                                  ((let uu____15763 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____15763
                                    then
                                      let uu____15764 =
                                        FStar_Syntax_Print.term_to_string t11
                                         in
                                      let uu____15765 = names_to_string fvs1
                                         in
                                      let uu____15766 = names_to_string fvs2
                                         in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitate_or_project\n"
                                        uu____15764 uu____15765 uu____15766
                                    else ());
                                   (let uu____15768 = subterms args_lhs  in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) lhs1 t21
                                      uu____15768))
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
                     (let uu____15779 =
                        let uu____15780 = FStar_Syntax_Free.names t1  in
                        check_head uu____15780 t2  in
                      if uu____15779
                      then
                        let n_args_lhs = FStar_List.length args_lhs  in
                        ((let uu____15791 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel")
                             in
                          if uu____15791
                          then
                            let uu____15792 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____15793 =
                              FStar_Util.string_of_int n_args_lhs  in
                            FStar_Util.print2
                              "Not a pattern (%s) ... (lhs has %s args)\n"
                              uu____15792 uu____15793
                          else ());
                         (let uu____15801 = subterms args_lhs  in
                          pattern_eq_imitate_or_project n_args_lhs
                            (FStar_Pervasives_Native.fst lhs) t2 uu____15801))
                      else giveup env "head-symbol is free" orig))
           in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let solve_both_pats wl1 uu____15878 uu____15879 r =
               match (uu____15878, uu____15879) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____16077 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys)
                      in
                   if uu____16077
                   then
                     let uu____16078 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1
                        in
                     solve env uu____16078
                   else
                     (let xs1 = sn_binders env xs  in
                      let ys1 = sn_binders env ys  in
                      let zs = intersect_vars xs1 ys1  in
                      (let uu____16102 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____16102
                       then
                         let uu____16103 =
                           FStar_Syntax_Print.binders_to_string ", " xs1  in
                         let uu____16104 =
                           FStar_Syntax_Print.binders_to_string ", " ys1  in
                         let uu____16105 =
                           FStar_Syntax_Print.binders_to_string ", " zs  in
                         let uu____16106 =
                           FStar_Syntax_Print.term_to_string k1  in
                         let uu____16107 =
                           FStar_Syntax_Print.term_to_string k2  in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____16103 uu____16104 uu____16105 uu____16106
                           uu____16107
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2  in
                         let args_len = FStar_List.length args  in
                         if xs_len = args_len
                         then
                           let uu____16167 =
                             FStar_Syntax_Util.subst_of_list xs2 args  in
                           FStar_Syntax_Subst.subst uu____16167 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____16181 =
                                FStar_Util.first_N args_len xs2  in
                              match uu____16181 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____16235 =
                                      FStar_Syntax_Syntax.mk_GTotal k  in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____16235
                                     in
                                  let uu____16238 =
                                    FStar_Syntax_Util.subst_of_list xs3 args
                                     in
                                  FStar_Syntax_Subst.subst uu____16238 k3)
                           else
                             (let uu____16242 =
                                let uu____16243 =
                                  FStar_Syntax_Print.term_to_string k  in
                                let uu____16244 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2
                                   in
                                let uu____16245 =
                                  FStar_Syntax_Print.args_to_string args  in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____16243 uu____16244 uu____16245
                                 in
                              failwith uu____16242)
                          in
                       let uu____16246 =
                         let uu____16253 =
                           let uu____16266 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1
                              in
                           FStar_Syntax_Util.arrow_formals uu____16266  in
                         match uu____16253 with
                         | (bs,k1') ->
                             let uu____16291 =
                               let uu____16304 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2
                                  in
                               FStar_Syntax_Util.arrow_formals uu____16304
                                in
                             (match uu____16291 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1  in
                                  let k2'_ys = subst_k k2' cs args2  in
                                  let sub_prob =
                                    let uu____16332 =
                                      let uu____16337 = p_scope orig  in
                                      mk_problem uu____16337 orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____16332
                                     in
                                  let uu____16342 =
                                    let uu____16347 =
                                      let uu____16348 =
                                        FStar_Syntax_Subst.compress k1'  in
                                      uu____16348.FStar_Syntax_Syntax.n  in
                                    let uu____16351 =
                                      let uu____16352 =
                                        FStar_Syntax_Subst.compress k2'  in
                                      uu____16352.FStar_Syntax_Syntax.n  in
                                    (uu____16347, uu____16351)  in
                                  (match uu____16342 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____16361,uu____16362) ->
                                       (k1'_xs, [sub_prob])
                                   | (uu____16365,FStar_Syntax_Syntax.Tm_type
                                      uu____16366) -> (k2'_ys, [sub_prob])
                                   | uu____16369 ->
                                       let uu____16374 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____16374 with
                                        | (t,uu____16386) ->
                                            let uu____16387 = new_uvar r zs t
                                               in
                                            (match uu____16387 with
                                             | (k_zs,uu____16399) ->
                                                 let kprob =
                                                   let uu____16401 =
                                                     let uu____16406 =
                                                       p_scope orig  in
                                                     mk_problem uu____16406
                                                       orig k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs
                                                       FStar_Pervasives_Native.None
                                                       "flex-flex kinding"
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_64  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_64) uu____16401
                                                    in
                                                 (k_zs, [sub_prob; kprob])))))
                          in
                       match uu____16246 with
                       | (k_u',sub_probs) ->
                           let uu____16419 =
                             let uu____16430 =
                               let uu____16431 = new_uvar r zs k_u'  in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____16431
                                in
                             let uu____16440 =
                               let uu____16443 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow xs1 uu____16443  in
                             let uu____16446 =
                               let uu____16449 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow ys1 uu____16449  in
                             (uu____16430, uu____16440, uu____16446)  in
                           (match uu____16419 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs  in
                                let uu____16468 =
                                  occurs_check env wl1 (u1, k1) sub1  in
                                (match uu____16468 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1)  in
                                        let uu____16487 =
                                          FStar_Syntax_Unionfind.equiv u1 u2
                                           in
                                        if uu____16487
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
                                           let uu____16491 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2
                                              in
                                           match uu____16491 with
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
             let solve_one_pat uu____16544 uu____16545 =
               match (uu____16544, uu____16545) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____16663 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____16663
                     then
                       let uu____16664 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____16665 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____16664 uu____16665
                     else ());
                    (let uu____16667 = FStar_Syntax_Unionfind.equiv u1 u2  in
                     if uu____16667
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____16686  ->
                              fun uu____16687  ->
                                match (uu____16686, uu____16687) with
                                | ((a,uu____16705),(t21,uu____16707)) ->
                                    let uu____16716 =
                                      let uu____16721 = p_scope orig  in
                                      let uu____16722 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      mk_problem uu____16721 orig uu____16722
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index"
                                       in
                                    FStar_All.pipe_right uu____16716
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2
                          in
                       let guard =
                         let uu____16728 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____16728  in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl
                          in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2  in
                        let rhs_vars = FStar_Syntax_Free.names t21  in
                        let uu____16743 = occurs_check env wl (u1, k1) t21
                           in
                        match uu____16743 with
                        | (occurs_ok,uu____16751) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs  in
                            let uu____16759 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars)
                               in
                            if uu____16759
                            then
                              let sol =
                                let uu____16761 =
                                  let uu____16770 = u_abs k1 xs t21  in
                                  ((u1, k1), uu____16770)  in
                                TERM uu____16761  in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl
                                 in
                              solve env wl1
                            else
                              (let uu____16777 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok)
                                  in
                               if uu____16777
                               then
                                 let uu____16778 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2)
                                    in
                                 match uu____16778 with
                                 | FStar_Pervasives_Native.None  ->
                                     giveup_or_defer1 orig
                                       "flex-flex constraint"
                                 | FStar_Pervasives_Native.Some
                                     (sol,(uu____16802,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl
                                        in
                                     ((let uu____16828 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern")
                                          in
                                       if uu____16828
                                       then
                                         let uu____16829 =
                                           uvi_to_string env sol  in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____16829
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____16836 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint"))))
                in
             let uu____16838 = lhs  in
             match uu____16838 with
             | (t1,u1,k1,args1) ->
                 let uu____16843 = rhs  in
                 (match uu____16843 with
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
                       | uu____16883 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____16893 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1)
                                 in
                              match uu____16893 with
                              | FStar_Pervasives_Native.None  ->
                                  giveup env
                                    "flex-flex: neither side is a pattern, nor is coercible to a pattern"
                                    orig
                              | FStar_Pervasives_Native.Some
                                  (sol,uu____16911) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl  in
                                  ((let uu____16918 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern")
                                       in
                                    if uu____16918
                                    then
                                      let uu____16919 = uvi_to_string env sol
                                         in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____16919
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____16926 ->
                                        giveup env "impossible" orig))))))
           in
        let orig = FStar_TypeChecker_Common.TProb problem  in
        let uu____16928 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs
           in
        if uu____16928
        then
          let uu____16929 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____16929
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs  in
           let t2 = problem.FStar_TypeChecker_Common.rhs  in
           let uu____16933 = FStar_Util.physical_equality t1 t2  in
           if uu____16933
           then
             let uu____16934 =
               solve_prob orig FStar_Pervasives_Native.None [] wl  in
             solve env uu____16934
           else
             ((let uu____16937 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck")
                  in
               if uu____16937
               then
                 let uu____16938 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid
                    in
                 let uu____16939 = FStar_Syntax_Print.tag_of_term t1  in
                 let uu____16940 = FStar_Syntax_Print.tag_of_term t2  in
                 FStar_Util.print3 "Attempting %s (%s - %s)\n" uu____16938
                   uu____16939 uu____16940
               else ());
              (let r = FStar_TypeChecker_Env.get_range env  in
               let not_quote t =
                 let uu____16947 =
                   let uu____16948 = FStar_Syntax_Subst.compress t  in
                   uu____16948.FStar_Syntax_Syntax.n  in
                 match uu____16947 with
                 | FStar_Syntax_Syntax.Tm_meta
                     (uu____16951,FStar_Syntax_Syntax.Meta_quoted
                      uu____16952)
                     -> false
                 | uu____16963 -> true  in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_delayed uu____16964,uu____16965) ->
                   failwith "Impossible: terms were not compressed"
               | (uu____16990,FStar_Syntax_Syntax.Tm_delayed uu____16991) ->
                   failwith "Impossible: terms were not compressed"
               | (FStar_Syntax_Syntax.Tm_ascribed uu____17016,uu____17017) ->
                   let uu____17044 =
                     let uu___148_17045 = problem  in
                     let uu____17046 = FStar_Syntax_Util.unascribe t1  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___148_17045.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____17046;
                       FStar_TypeChecker_Common.relation =
                         (uu___148_17045.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___148_17045.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___148_17045.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___148_17045.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___148_17045.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___148_17045.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___148_17045.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___148_17045.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____17044 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____17047,uu____17048) when
                   not_quote t1 ->
                   let uu____17055 =
                     let uu___149_17056 = problem  in
                     let uu____17057 = FStar_Syntax_Util.unmeta t1  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___149_17056.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____17057;
                       FStar_TypeChecker_Common.relation =
                         (uu___149_17056.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___149_17056.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___149_17056.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___149_17056.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___149_17056.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___149_17056.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___149_17056.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___149_17056.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____17055 wl
               | (uu____17058,FStar_Syntax_Syntax.Tm_ascribed uu____17059) ->
                   let uu____17086 =
                     let uu___150_17087 = problem  in
                     let uu____17088 = FStar_Syntax_Util.unascribe t2  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___150_17087.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___150_17087.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___150_17087.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____17088;
                       FStar_TypeChecker_Common.element =
                         (uu___150_17087.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___150_17087.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___150_17087.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___150_17087.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___150_17087.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___150_17087.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____17086 wl
               | (uu____17089,FStar_Syntax_Syntax.Tm_meta uu____17090) when
                   not_quote t2 ->
                   let uu____17097 =
                     let uu___151_17098 = problem  in
                     let uu____17099 = FStar_Syntax_Util.unmeta t2  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___151_17098.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___151_17098.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___151_17098.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____17099;
                       FStar_TypeChecker_Common.element =
                         (uu___151_17098.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___151_17098.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___151_17098.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___151_17098.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___151_17098.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___151_17098.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____17097 wl
               | (FStar_Syntax_Syntax.Tm_meta
                  (uu____17100,FStar_Syntax_Syntax.Meta_quoted
                   (t11,uu____17102)),FStar_Syntax_Syntax.Tm_meta
                  (uu____17103,FStar_Syntax_Syntax.Meta_quoted
                   (t21,uu____17105))) ->
                   let uu____17122 =
                     solve_prob orig FStar_Pervasives_Native.None [] wl  in
                   solve env uu____17122
               | (FStar_Syntax_Syntax.Tm_bvar uu____17123,uu____17124) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____17125,FStar_Syntax_Syntax.Tm_bvar uu____17126) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___112_17181 =
                     match uu___112_17181 with
                     | [] -> c
                     | bs ->
                         let uu____17203 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos
                            in
                         FStar_Syntax_Syntax.mk_Total uu____17203
                      in
                   let uu____17212 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                   (match uu____17212 with
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
                                   let uu____17354 =
                                     FStar_Options.use_eq_at_higher_order ()
                                      in
                                   if uu____17354
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation
                                    in
                                 let uu____17356 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____17356))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___113_17432 =
                     match uu___113_17432 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos
                      in
                   let uu____17466 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2))
                      in
                   (match uu____17466 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____17602 =
                                   let uu____17607 =
                                     FStar_Syntax_Subst.subst subst1 tbody11
                                      in
                                   let uu____17608 =
                                     FStar_Syntax_Subst.subst subst1 tbody21
                                      in
                                   mk_problem scope orig uu____17607
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____17608 FStar_Pervasives_Native.None
                                     "lambda co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____17602))
               | (FStar_Syntax_Syntax.Tm_abs uu____17613,uu____17614) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17639 -> true
                     | uu____17656 -> false  in
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
                       (let uu____17703 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___152_17711 = env  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___152_17711.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___152_17711.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___152_17711.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___152_17711.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___152_17711.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___152_17711.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___152_17711.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___152_17711.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___152_17711.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___152_17711.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___152_17711.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___152_17711.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___152_17711.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___152_17711.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___152_17711.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___152_17711.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___152_17711.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___152_17711.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___152_17711.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___152_17711.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___152_17711.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___152_17711.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___152_17711.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___152_17711.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___152_17711.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___152_17711.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___152_17711.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.splice =
                                 (uu___152_17711.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___152_17711.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___152_17711.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___152_17711.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___152_17711.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___152_17711.FStar_TypeChecker_Env.dep_graph)
                             }) t
                           in
                        match uu____17703 with
                        | (uu____17714,ty,uu____17716) ->
                            let uu____17717 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty
                               in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17717)
                      in
                   let uu____17718 =
                     let uu____17735 = maybe_eta t1  in
                     let uu____17742 = maybe_eta t2  in
                     (uu____17735, uu____17742)  in
                   (match uu____17718 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___153_17784 = problem  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___153_17784.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___153_17784.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___153_17784.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___153_17784.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___153_17784.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___153_17784.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___153_17784.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___153_17784.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____17807 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____17807
                        then
                          let uu____17808 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____17808 t_abs wl
                        else
                          (let t11 = force_eta t1  in
                           let t21 = force_eta t2  in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___154_17823 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___154_17823.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___154_17823.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___154_17823.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___154_17823.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___154_17823.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___154_17823.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___154_17823.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___154_17823.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____17847 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____17847
                        then
                          let uu____17848 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____17848 t_abs wl
                        else
                          (let t11 = force_eta t1  in
                           let t21 = force_eta t2  in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___154_17863 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___154_17863.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___154_17863.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___154_17863.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___154_17863.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___154_17863.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___154_17863.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___154_17863.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___154_17863.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____17867 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____17884,FStar_Syntax_Syntax.Tm_abs uu____17885) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____17910 -> true
                     | uu____17927 -> false  in
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
                       (let uu____17974 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___152_17982 = env  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___152_17982.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___152_17982.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___152_17982.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___152_17982.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___152_17982.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___152_17982.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 FStar_Pervasives_Native.None;
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___152_17982.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___152_17982.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___152_17982.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___152_17982.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___152_17982.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___152_17982.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___152_17982.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___152_17982.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___152_17982.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___152_17982.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___152_17982.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___152_17982.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___152_17982.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___152_17982.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___152_17982.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___152_17982.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___152_17982.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___152_17982.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___152_17982.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___152_17982.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___152_17982.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.splice =
                                 (uu___152_17982.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___152_17982.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___152_17982.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___152_17982.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___152_17982.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.dep_graph =
                                 (uu___152_17982.FStar_TypeChecker_Env.dep_graph)
                             }) t
                           in
                        match uu____17974 with
                        | (uu____17985,ty,uu____17987) ->
                            let uu____17988 =
                              FStar_TypeChecker_Normalize.unfold_whnf env ty
                               in
                            FStar_TypeChecker_Normalize.eta_expand_with_type
                              env t uu____17988)
                      in
                   let uu____17989 =
                     let uu____18006 = maybe_eta t1  in
                     let uu____18013 = maybe_eta t2  in
                     (uu____18006, uu____18013)  in
                   (match uu____17989 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___153_18055 = problem  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___153_18055.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___153_18055.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___153_18055.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___153_18055.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___153_18055.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___153_18055.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___153_18055.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___153_18055.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____18078 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____18078
                        then
                          let uu____18079 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____18079 t_abs wl
                        else
                          (let t11 = force_eta t1  in
                           let t21 = force_eta t2  in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___154_18094 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___154_18094.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___154_18094.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___154_18094.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___154_18094.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___154_18094.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___154_18094.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___154_18094.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___154_18094.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____18118 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____18118
                        then
                          let uu____18119 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____18119 t_abs wl
                        else
                          (let t11 = force_eta t1  in
                           let t21 = force_eta t2  in
                           if (is_abs t11) && (is_abs t21)
                           then
                             solve_t env
                               (let uu___154_18134 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___154_18134.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = t11;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___154_18134.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t21;
                                  FStar_TypeChecker_Common.element =
                                    (uu___154_18134.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___154_18134.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.scope =
                                    (uu___154_18134.FStar_TypeChecker_Common.scope);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___154_18134.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___154_18134.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___154_18134.FStar_TypeChecker_Common.rank)
                                }) wl
                           else
                             giveup env
                               "head tag mismatch: RHS is an abstraction"
                               orig)
                    | uu____18138 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                   let should_delta =
                     ((let uu____18170 = FStar_Syntax_Free.uvars t1  in
                       FStar_Util.set_is_empty uu____18170) &&
                        (let uu____18182 = FStar_Syntax_Free.uvars t2  in
                         FStar_Util.set_is_empty uu____18182))
                       &&
                       (let uu____18197 =
                          head_matches env x1.FStar_Syntax_Syntax.sort
                            x2.FStar_Syntax_Syntax.sort
                           in
                        match uu____18197 with
                        | MisMatch
                            (FStar_Pervasives_Native.Some
                             d1,FStar_Pervasives_Native.Some d2)
                            ->
                            let is_unfoldable uu___114_18207 =
                              match uu___114_18207 with
                              | FStar_Syntax_Syntax.Delta_constant  -> true
                              | FStar_Syntax_Syntax.Delta_defined_at_level
                                  uu____18208 -> true
                              | uu____18209 -> false  in
                            (is_unfoldable d1) && (is_unfoldable d2)
                        | uu____18210 -> false)
                      in
                   let uu____18211 = as_refinement should_delta env wl t1  in
                   (match uu____18211 with
                    | (x11,phi1) ->
                        let uu____18218 =
                          as_refinement should_delta env wl t2  in
                        (match uu____18218 with
                         | (x21,phi21) ->
                             let base_prob =
                               let uu____18226 =
                                 let uu____18231 = p_scope orig  in
                                 mk_problem uu____18231 orig
                                   x11.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x21.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____18226
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
                               let uu____18265 = imp phi12 phi23  in
                               FStar_All.pipe_right uu____18265
                                 (guard_on_element wl problem x12)
                                in
                             let fallback uu____18269 =
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
                                 let uu____18275 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____18275 impl
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
                                 let uu____18284 =
                                   let uu____18289 =
                                     let uu____18290 = p_scope orig  in
                                     let uu____18297 =
                                       let uu____18304 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____18304]  in
                                     FStar_List.append uu____18290
                                       uu____18297
                                      in
                                   mk_problem uu____18289 orig phi11
                                     FStar_TypeChecker_Common.EQ phi22
                                     FStar_Pervasives_Native.None
                                     "refinement formula"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____18284
                                  in
                               let uu____18313 =
                                 solve env1
                                   (let uu___155_18315 = wl  in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___155_18315.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___155_18315.smt_ok);
                                      tcenv = (uu___155_18315.tcenv)
                                    })
                                  in
                               (match uu____18313 with
                                | Failed uu____18322 -> fallback ()
                                | Success uu____18327 ->
                                    let guard =
                                      let uu____18331 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      let uu____18336 =
                                        let uu____18337 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____18337
                                          (guard_on_element wl problem x12)
                                         in
                                      FStar_Syntax_Util.mk_conj uu____18331
                                        uu____18336
                                       in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl
                                       in
                                    let wl2 =
                                      let uu___156_18346 = wl1  in
                                      {
                                        attempting =
                                          (uu___156_18346.attempting);
                                        wl_deferred =
                                          (uu___156_18346.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___156_18346.defer_ok);
                                        smt_ok = (uu___156_18346.smt_ok);
                                        tcenv = (uu___156_18346.tcenv)
                                      }  in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18348,FStar_Syntax_Syntax.Tm_uvar uu____18349) ->
                   let uu____18382 = destruct_flex_t t1  in
                   let uu____18383 = destruct_flex_t t2  in
                   flex_flex1 orig uu____18382 uu____18383
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18384;
                     FStar_Syntax_Syntax.pos = uu____18385;
                     FStar_Syntax_Syntax.vars = uu____18386;_},uu____18387),FStar_Syntax_Syntax.Tm_uvar
                  uu____18388) ->
                   let uu____18441 = destruct_flex_t t1  in
                   let uu____18442 = destruct_flex_t t2  in
                   flex_flex1 orig uu____18441 uu____18442
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18443,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18444;
                     FStar_Syntax_Syntax.pos = uu____18445;
                     FStar_Syntax_Syntax.vars = uu____18446;_},uu____18447))
                   ->
                   let uu____18500 = destruct_flex_t t1  in
                   let uu____18501 = destruct_flex_t t2  in
                   flex_flex1 orig uu____18500 uu____18501
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18502;
                     FStar_Syntax_Syntax.pos = uu____18503;
                     FStar_Syntax_Syntax.vars = uu____18504;_},uu____18505),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18506;
                     FStar_Syntax_Syntax.pos = uu____18507;
                     FStar_Syntax_Syntax.vars = uu____18508;_},uu____18509))
                   ->
                   let uu____18582 = destruct_flex_t t1  in
                   let uu____18583 = destruct_flex_t t2  in
                   flex_flex1 orig uu____18582 uu____18583
               | (FStar_Syntax_Syntax.Tm_uvar uu____18584,uu____18585) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18602 = destruct_flex_pattern env t1  in
                   solve_t_flex_rigid false orig uu____18602 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18609;
                     FStar_Syntax_Syntax.pos = uu____18610;
                     FStar_Syntax_Syntax.vars = uu____18611;_},uu____18612),uu____18613)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____18650 = destruct_flex_pattern env t1  in
                   solve_t_flex_rigid false orig uu____18650 t2 wl
               | (uu____18657,FStar_Syntax_Syntax.Tm_uvar uu____18658) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____18675,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18676;
                     FStar_Syntax_Syntax.pos = uu____18677;
                     FStar_Syntax_Syntax.vars = uu____18678;_},uu____18679))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18716,FStar_Syntax_Syntax.Tm_type uu____18717) ->
                   solve_t' env
                     (let uu___157_18735 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___157_18735.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___157_18735.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___157_18735.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___157_18735.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___157_18735.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___157_18735.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___157_18735.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___157_18735.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___157_18735.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18736;
                     FStar_Syntax_Syntax.pos = uu____18737;
                     FStar_Syntax_Syntax.vars = uu____18738;_},uu____18739),FStar_Syntax_Syntax.Tm_type
                  uu____18740) ->
                   solve_t' env
                     (let uu___157_18778 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___157_18778.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___157_18778.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___157_18778.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___157_18778.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___157_18778.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___157_18778.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___157_18778.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___157_18778.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___157_18778.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____18779,FStar_Syntax_Syntax.Tm_arrow uu____18780) ->
                   solve_t' env
                     (let uu___157_18810 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___157_18810.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___157_18810.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___157_18810.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___157_18810.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___157_18810.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___157_18810.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___157_18810.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___157_18810.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___157_18810.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____18811;
                     FStar_Syntax_Syntax.pos = uu____18812;
                     FStar_Syntax_Syntax.vars = uu____18813;_},uu____18814),FStar_Syntax_Syntax.Tm_arrow
                  uu____18815) ->
                   solve_t' env
                     (let uu___157_18865 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___157_18865.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___157_18865.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___157_18865.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___157_18865.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___157_18865.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___157_18865.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___157_18865.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___157_18865.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___157_18865.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____18866,uu____18867) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation
                         in
                      let uu____18886 =
                        let uu____18887 = is_top_level_prob orig  in
                        FStar_All.pipe_left Prims.op_Negation uu____18887  in
                      if uu____18886
                      then
                        let uu____18888 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___158_18894 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___158_18894.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___158_18894.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___158_18894.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___158_18894.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___158_18894.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___158_18894.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___158_18894.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___158_18894.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___158_18894.FStar_TypeChecker_Common.rank)
                             })
                           in
                        let uu____18895 = destruct_flex_pattern env t1  in
                        solve_t_flex_rigid false uu____18888 uu____18895 t2
                          wl
                      else
                        (let uu____18903 = base_and_refinement env t2  in
                         match uu____18903 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____18932 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___159_18938 = problem  in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___159_18938.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___159_18938.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___159_18938.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___159_18938.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___159_18938.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___159_18938.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___159_18938.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___159_18938.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___159_18938.FStar_TypeChecker_Common.rank)
                                       })
                                     in
                                  let uu____18939 =
                                    destruct_flex_pattern env t1  in
                                  solve_t_flex_rigid false uu____18932
                                    uu____18939 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___160_18953 = y  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___160_18953.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___160_18953.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }  in
                                  let impl =
                                    guard_on_element wl problem y' phi  in
                                  let base_prob =
                                    let uu____18956 =
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
                                      uu____18956
                                     in
                                  let guard =
                                    let uu____18968 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Util.mk_conj uu____18968
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
                       uu____18976;
                     FStar_Syntax_Syntax.pos = uu____18977;
                     FStar_Syntax_Syntax.vars = uu____18978;_},uu____18979),uu____18980)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation
                         in
                      let uu____19019 =
                        let uu____19020 = is_top_level_prob orig  in
                        FStar_All.pipe_left Prims.op_Negation uu____19020  in
                      if uu____19019
                      then
                        let uu____19021 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___158_19027 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___158_19027.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___158_19027.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___158_19027.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___158_19027.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___158_19027.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___158_19027.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___158_19027.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___158_19027.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___158_19027.FStar_TypeChecker_Common.rank)
                             })
                           in
                        let uu____19028 = destruct_flex_pattern env t1  in
                        solve_t_flex_rigid false uu____19021 uu____19028 t2
                          wl
                      else
                        (let uu____19036 = base_and_refinement env t2  in
                         match uu____19036 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____19065 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___159_19071 = problem  in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___159_19071.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___159_19071.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___159_19071.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___159_19071.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___159_19071.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___159_19071.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___159_19071.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___159_19071.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___159_19071.FStar_TypeChecker_Common.rank)
                                       })
                                     in
                                  let uu____19072 =
                                    destruct_flex_pattern env t1  in
                                  solve_t_flex_rigid false uu____19065
                                    uu____19072 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___160_19086 = y  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___160_19086.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___160_19086.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }  in
                                  let impl =
                                    guard_on_element wl problem y' phi  in
                                  let base_prob =
                                    let uu____19089 =
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
                                      uu____19089
                                     in
                                  let guard =
                                    let uu____19101 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Util.mk_conj uu____19101
                                      impl
                                     in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl
                                     in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____19109,FStar_Syntax_Syntax.Tm_uvar uu____19110) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____19128 = base_and_refinement env t1  in
                      match uu____19128 with
                      | (t_base,uu____19140) ->
                          solve_t env
                            (let uu___161_19154 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___161_19154.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___161_19154.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___161_19154.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___161_19154.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___161_19154.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___161_19154.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___161_19154.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___161_19154.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____19155,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____19156;
                     FStar_Syntax_Syntax.pos = uu____19157;
                     FStar_Syntax_Syntax.vars = uu____19158;_},uu____19159))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____19197 = base_and_refinement env t1  in
                      match uu____19197 with
                      | (t_base,uu____19209) ->
                          solve_t env
                            (let uu___161_19223 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___161_19223.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___161_19223.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___161_19223.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___161_19223.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___161_19223.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___161_19223.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___161_19223.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___161_19223.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____19224,uu____19225) ->
                   let t21 =
                     let uu____19235 = base_and_refinement env t2  in
                     FStar_All.pipe_left force_refinement uu____19235  in
                   solve_t env
                     (let uu___162_19259 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___162_19259.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___162_19259.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___162_19259.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___162_19259.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___162_19259.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___162_19259.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___162_19259.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___162_19259.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___162_19259.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____19260,FStar_Syntax_Syntax.Tm_refine uu____19261) ->
                   let t11 =
                     let uu____19271 = base_and_refinement env t1  in
                     FStar_All.pipe_left force_refinement uu____19271  in
                   solve_t env
                     (let uu___163_19295 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___163_19295.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___163_19295.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___163_19295.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___163_19295.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___163_19295.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___163_19295.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___163_19295.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___163_19295.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___163_19295.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____19298,uu____19299) ->
                   let head1 =
                     let uu____19325 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19325
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19369 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19369
                       FStar_Pervasives_Native.fst
                      in
                   ((let uu____19411 =
                       FStar_TypeChecker_Env.debug env
                         (FStar_Options.Other "RelCheck")
                        in
                     if uu____19411
                     then
                       let uu____19412 =
                         FStar_Util.string_of_int
                           problem.FStar_TypeChecker_Common.pid
                          in
                       let uu____19413 =
                         FStar_Syntax_Print.term_to_string head1  in
                       let uu____19414 =
                         FStar_Syntax_Print.term_to_string head2  in
                       FStar_Util.print3
                         ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                         uu____19412 uu____19413 uu____19414
                     else ());
                    (let uu____19416 =
                       (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          && wl.smt_ok)
                         &&
                         (problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ)
                        in
                     if uu____19416
                     then
                       let uv1 = FStar_Syntax_Free.uvars t1  in
                       let uv2 = FStar_Syntax_Free.uvars t2  in
                       let uu____19431 =
                         (FStar_Util.set_is_empty uv1) &&
                           (FStar_Util.set_is_empty uv2)
                          in
                       (if uu____19431
                        then
                          let guard =
                            let uu____19443 =
                              let uu____19444 = FStar_Syntax_Util.eq_tm t1 t2
                                 in
                              uu____19444 = FStar_Syntax_Util.Equal  in
                            if uu____19443
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____19448 = mk_eq2 env t1 t2  in
                               FStar_All.pipe_left
                                 (fun _0_76  ->
                                    FStar_Pervasives_Native.Some _0_76)
                                 uu____19448)
                             in
                          let uu____19451 = solve_prob orig guard [] wl  in
                          solve env uu____19451
                        else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2))
               | (FStar_Syntax_Syntax.Tm_uinst uu____19454,uu____19455) ->
                   let head1 =
                     let uu____19465 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19465
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19509 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19509
                       FStar_Pervasives_Native.fst
                      in
                   ((let uu____19551 =
                       FStar_TypeChecker_Env.debug env
                         (FStar_Options.Other "RelCheck")
                        in
                     if uu____19551
                     then
                       let uu____19552 =
                         FStar_Util.string_of_int
                           problem.FStar_TypeChecker_Common.pid
                          in
                       let uu____19553 =
                         FStar_Syntax_Print.term_to_string head1  in
                       let uu____19554 =
                         FStar_Syntax_Print.term_to_string head2  in
                       FStar_Util.print3
                         ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                         uu____19552 uu____19553 uu____19554
                     else ());
                    (let uu____19556 =
                       (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          && wl.smt_ok)
                         &&
                         (problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ)
                        in
                     if uu____19556
                     then
                       let uv1 = FStar_Syntax_Free.uvars t1  in
                       let uv2 = FStar_Syntax_Free.uvars t2  in
                       let uu____19571 =
                         (FStar_Util.set_is_empty uv1) &&
                           (FStar_Util.set_is_empty uv2)
                          in
                       (if uu____19571
                        then
                          let guard =
                            let uu____19583 =
                              let uu____19584 = FStar_Syntax_Util.eq_tm t1 t2
                                 in
                              uu____19584 = FStar_Syntax_Util.Equal  in
                            if uu____19583
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____19588 = mk_eq2 env t1 t2  in
                               FStar_All.pipe_left
                                 (fun _0_77  ->
                                    FStar_Pervasives_Native.Some _0_77)
                                 uu____19588)
                             in
                          let uu____19591 = solve_prob orig guard [] wl  in
                          solve env uu____19591
                        else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2))
               | (FStar_Syntax_Syntax.Tm_name uu____19594,uu____19595) ->
                   let head1 =
                     let uu____19599 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19599
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19643 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19643
                       FStar_Pervasives_Native.fst
                      in
                   ((let uu____19685 =
                       FStar_TypeChecker_Env.debug env
                         (FStar_Options.Other "RelCheck")
                        in
                     if uu____19685
                     then
                       let uu____19686 =
                         FStar_Util.string_of_int
                           problem.FStar_TypeChecker_Common.pid
                          in
                       let uu____19687 =
                         FStar_Syntax_Print.term_to_string head1  in
                       let uu____19688 =
                         FStar_Syntax_Print.term_to_string head2  in
                       FStar_Util.print3
                         ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                         uu____19686 uu____19687 uu____19688
                     else ());
                    (let uu____19690 =
                       (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          && wl.smt_ok)
                         &&
                         (problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ)
                        in
                     if uu____19690
                     then
                       let uv1 = FStar_Syntax_Free.uvars t1  in
                       let uv2 = FStar_Syntax_Free.uvars t2  in
                       let uu____19705 =
                         (FStar_Util.set_is_empty uv1) &&
                           (FStar_Util.set_is_empty uv2)
                          in
                       (if uu____19705
                        then
                          let guard =
                            let uu____19717 =
                              let uu____19718 = FStar_Syntax_Util.eq_tm t1 t2
                                 in
                              uu____19718 = FStar_Syntax_Util.Equal  in
                            if uu____19717
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____19722 = mk_eq2 env t1 t2  in
                               FStar_All.pipe_left
                                 (fun _0_78  ->
                                    FStar_Pervasives_Native.Some _0_78)
                                 uu____19722)
                             in
                          let uu____19725 = solve_prob orig guard [] wl  in
                          solve env uu____19725
                        else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2))
               | (FStar_Syntax_Syntax.Tm_constant uu____19728,uu____19729) ->
                   let head1 =
                     let uu____19733 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19733
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19777 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19777
                       FStar_Pervasives_Native.fst
                      in
                   ((let uu____19819 =
                       FStar_TypeChecker_Env.debug env
                         (FStar_Options.Other "RelCheck")
                        in
                     if uu____19819
                     then
                       let uu____19820 =
                         FStar_Util.string_of_int
                           problem.FStar_TypeChecker_Common.pid
                          in
                       let uu____19821 =
                         FStar_Syntax_Print.term_to_string head1  in
                       let uu____19822 =
                         FStar_Syntax_Print.term_to_string head2  in
                       FStar_Util.print3
                         ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                         uu____19820 uu____19821 uu____19822
                     else ());
                    (let uu____19824 =
                       (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          && wl.smt_ok)
                         &&
                         (problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ)
                        in
                     if uu____19824
                     then
                       let uv1 = FStar_Syntax_Free.uvars t1  in
                       let uv2 = FStar_Syntax_Free.uvars t2  in
                       let uu____19839 =
                         (FStar_Util.set_is_empty uv1) &&
                           (FStar_Util.set_is_empty uv2)
                          in
                       (if uu____19839
                        then
                          let guard =
                            let uu____19851 =
                              let uu____19852 = FStar_Syntax_Util.eq_tm t1 t2
                                 in
                              uu____19852 = FStar_Syntax_Util.Equal  in
                            if uu____19851
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____19856 = mk_eq2 env t1 t2  in
                               FStar_All.pipe_left
                                 (fun _0_79  ->
                                    FStar_Pervasives_Native.Some _0_79)
                                 uu____19856)
                             in
                          let uu____19859 = solve_prob orig guard [] wl  in
                          solve env uu____19859
                        else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2))
               | (FStar_Syntax_Syntax.Tm_fvar uu____19862,uu____19863) ->
                   let head1 =
                     let uu____19867 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____19867
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____19911 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____19911
                       FStar_Pervasives_Native.fst
                      in
                   ((let uu____19953 =
                       FStar_TypeChecker_Env.debug env
                         (FStar_Options.Other "RelCheck")
                        in
                     if uu____19953
                     then
                       let uu____19954 =
                         FStar_Util.string_of_int
                           problem.FStar_TypeChecker_Common.pid
                          in
                       let uu____19955 =
                         FStar_Syntax_Print.term_to_string head1  in
                       let uu____19956 =
                         FStar_Syntax_Print.term_to_string head2  in
                       FStar_Util.print3
                         ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                         uu____19954 uu____19955 uu____19956
                     else ());
                    (let uu____19958 =
                       (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          && wl.smt_ok)
                         &&
                         (problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ)
                        in
                     if uu____19958
                     then
                       let uv1 = FStar_Syntax_Free.uvars t1  in
                       let uv2 = FStar_Syntax_Free.uvars t2  in
                       let uu____19973 =
                         (FStar_Util.set_is_empty uv1) &&
                           (FStar_Util.set_is_empty uv2)
                          in
                       (if uu____19973
                        then
                          let guard =
                            let uu____19985 =
                              let uu____19986 = FStar_Syntax_Util.eq_tm t1 t2
                                 in
                              uu____19986 = FStar_Syntax_Util.Equal  in
                            if uu____19985
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____19990 = mk_eq2 env t1 t2  in
                               FStar_All.pipe_left
                                 (fun _0_80  ->
                                    FStar_Pervasives_Native.Some _0_80)
                                 uu____19990)
                             in
                          let uu____19993 = solve_prob orig guard [] wl  in
                          solve env uu____19993
                        else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2))
               | (FStar_Syntax_Syntax.Tm_app uu____19996,uu____19997) ->
                   let head1 =
                     let uu____20015 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20015
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20059 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20059
                       FStar_Pervasives_Native.fst
                      in
                   ((let uu____20101 =
                       FStar_TypeChecker_Env.debug env
                         (FStar_Options.Other "RelCheck")
                        in
                     if uu____20101
                     then
                       let uu____20102 =
                         FStar_Util.string_of_int
                           problem.FStar_TypeChecker_Common.pid
                          in
                       let uu____20103 =
                         FStar_Syntax_Print.term_to_string head1  in
                       let uu____20104 =
                         FStar_Syntax_Print.term_to_string head2  in
                       FStar_Util.print3
                         ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                         uu____20102 uu____20103 uu____20104
                     else ());
                    (let uu____20106 =
                       (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          && wl.smt_ok)
                         &&
                         (problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ)
                        in
                     if uu____20106
                     then
                       let uv1 = FStar_Syntax_Free.uvars t1  in
                       let uv2 = FStar_Syntax_Free.uvars t2  in
                       let uu____20121 =
                         (FStar_Util.set_is_empty uv1) &&
                           (FStar_Util.set_is_empty uv2)
                          in
                       (if uu____20121
                        then
                          let guard =
                            let uu____20133 =
                              let uu____20134 = FStar_Syntax_Util.eq_tm t1 t2
                                 in
                              uu____20134 = FStar_Syntax_Util.Equal  in
                            if uu____20133
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____20138 = mk_eq2 env t1 t2  in
                               FStar_All.pipe_left
                                 (fun _0_81  ->
                                    FStar_Pervasives_Native.Some _0_81)
                                 uu____20138)
                             in
                          let uu____20141 = solve_prob orig guard [] wl  in
                          solve env uu____20141
                        else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2))
               | (uu____20144,FStar_Syntax_Syntax.Tm_match uu____20145) ->
                   let head1 =
                     let uu____20171 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20171
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20215 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20215
                       FStar_Pervasives_Native.fst
                      in
                   ((let uu____20257 =
                       FStar_TypeChecker_Env.debug env
                         (FStar_Options.Other "RelCheck")
                        in
                     if uu____20257
                     then
                       let uu____20258 =
                         FStar_Util.string_of_int
                           problem.FStar_TypeChecker_Common.pid
                          in
                       let uu____20259 =
                         FStar_Syntax_Print.term_to_string head1  in
                       let uu____20260 =
                         FStar_Syntax_Print.term_to_string head2  in
                       FStar_Util.print3
                         ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                         uu____20258 uu____20259 uu____20260
                     else ());
                    (let uu____20262 =
                       (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          && wl.smt_ok)
                         &&
                         (problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ)
                        in
                     if uu____20262
                     then
                       let uv1 = FStar_Syntax_Free.uvars t1  in
                       let uv2 = FStar_Syntax_Free.uvars t2  in
                       let uu____20277 =
                         (FStar_Util.set_is_empty uv1) &&
                           (FStar_Util.set_is_empty uv2)
                          in
                       (if uu____20277
                        then
                          let guard =
                            let uu____20289 =
                              let uu____20290 = FStar_Syntax_Util.eq_tm t1 t2
                                 in
                              uu____20290 = FStar_Syntax_Util.Equal  in
                            if uu____20289
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____20294 = mk_eq2 env t1 t2  in
                               FStar_All.pipe_left
                                 (fun _0_82  ->
                                    FStar_Pervasives_Native.Some _0_82)
                                 uu____20294)
                             in
                          let uu____20297 = solve_prob orig guard [] wl  in
                          solve env uu____20297
                        else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2))
               | (uu____20300,FStar_Syntax_Syntax.Tm_uinst uu____20301) ->
                   let head1 =
                     let uu____20311 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20311
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20355 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20355
                       FStar_Pervasives_Native.fst
                      in
                   ((let uu____20397 =
                       FStar_TypeChecker_Env.debug env
                         (FStar_Options.Other "RelCheck")
                        in
                     if uu____20397
                     then
                       let uu____20398 =
                         FStar_Util.string_of_int
                           problem.FStar_TypeChecker_Common.pid
                          in
                       let uu____20399 =
                         FStar_Syntax_Print.term_to_string head1  in
                       let uu____20400 =
                         FStar_Syntax_Print.term_to_string head2  in
                       FStar_Util.print3
                         ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                         uu____20398 uu____20399 uu____20400
                     else ());
                    (let uu____20402 =
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
                                 (fun _0_83  ->
                                    FStar_Pervasives_Native.Some _0_83)
                                 uu____20434)
                             in
                          let uu____20437 = solve_prob orig guard [] wl  in
                          solve env uu____20437
                        else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2))
               | (uu____20440,FStar_Syntax_Syntax.Tm_name uu____20441) ->
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
                   ((let uu____20531 =
                       FStar_TypeChecker_Env.debug env
                         (FStar_Options.Other "RelCheck")
                        in
                     if uu____20531
                     then
                       let uu____20532 =
                         FStar_Util.string_of_int
                           problem.FStar_TypeChecker_Common.pid
                          in
                       let uu____20533 =
                         FStar_Syntax_Print.term_to_string head1  in
                       let uu____20534 =
                         FStar_Syntax_Print.term_to_string head2  in
                       FStar_Util.print3
                         ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                         uu____20532 uu____20533 uu____20534
                     else ());
                    (let uu____20536 =
                       (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          && wl.smt_ok)
                         &&
                         (problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ)
                        in
                     if uu____20536
                     then
                       let uv1 = FStar_Syntax_Free.uvars t1  in
                       let uv2 = FStar_Syntax_Free.uvars t2  in
                       let uu____20551 =
                         (FStar_Util.set_is_empty uv1) &&
                           (FStar_Util.set_is_empty uv2)
                          in
                       (if uu____20551
                        then
                          let guard =
                            let uu____20563 =
                              let uu____20564 = FStar_Syntax_Util.eq_tm t1 t2
                                 in
                              uu____20564 = FStar_Syntax_Util.Equal  in
                            if uu____20563
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____20568 = mk_eq2 env t1 t2  in
                               FStar_All.pipe_left
                                 (fun _0_84  ->
                                    FStar_Pervasives_Native.Some _0_84)
                                 uu____20568)
                             in
                          let uu____20571 = solve_prob orig guard [] wl  in
                          solve env uu____20571
                        else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2))
               | (uu____20574,FStar_Syntax_Syntax.Tm_constant uu____20575) ->
                   let head1 =
                     let uu____20579 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20579
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20623 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20623
                       FStar_Pervasives_Native.fst
                      in
                   ((let uu____20665 =
                       FStar_TypeChecker_Env.debug env
                         (FStar_Options.Other "RelCheck")
                        in
                     if uu____20665
                     then
                       let uu____20666 =
                         FStar_Util.string_of_int
                           problem.FStar_TypeChecker_Common.pid
                          in
                       let uu____20667 =
                         FStar_Syntax_Print.term_to_string head1  in
                       let uu____20668 =
                         FStar_Syntax_Print.term_to_string head2  in
                       FStar_Util.print3
                         ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                         uu____20666 uu____20667 uu____20668
                     else ());
                    (let uu____20670 =
                       (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          && wl.smt_ok)
                         &&
                         (problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ)
                        in
                     if uu____20670
                     then
                       let uv1 = FStar_Syntax_Free.uvars t1  in
                       let uv2 = FStar_Syntax_Free.uvars t2  in
                       let uu____20685 =
                         (FStar_Util.set_is_empty uv1) &&
                           (FStar_Util.set_is_empty uv2)
                          in
                       (if uu____20685
                        then
                          let guard =
                            let uu____20697 =
                              let uu____20698 = FStar_Syntax_Util.eq_tm t1 t2
                                 in
                              uu____20698 = FStar_Syntax_Util.Equal  in
                            if uu____20697
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____20702 = mk_eq2 env t1 t2  in
                               FStar_All.pipe_left
                                 (fun _0_85  ->
                                    FStar_Pervasives_Native.Some _0_85)
                                 uu____20702)
                             in
                          let uu____20705 = solve_prob orig guard [] wl  in
                          solve env uu____20705
                        else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2))
               | (uu____20708,FStar_Syntax_Syntax.Tm_fvar uu____20709) ->
                   let head1 =
                     let uu____20713 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20713
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20757 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20757
                       FStar_Pervasives_Native.fst
                      in
                   ((let uu____20799 =
                       FStar_TypeChecker_Env.debug env
                         (FStar_Options.Other "RelCheck")
                        in
                     if uu____20799
                     then
                       let uu____20800 =
                         FStar_Util.string_of_int
                           problem.FStar_TypeChecker_Common.pid
                          in
                       let uu____20801 =
                         FStar_Syntax_Print.term_to_string head1  in
                       let uu____20802 =
                         FStar_Syntax_Print.term_to_string head2  in
                       FStar_Util.print3
                         ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                         uu____20800 uu____20801 uu____20802
                     else ());
                    (let uu____20804 =
                       (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          && wl.smt_ok)
                         &&
                         (problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ)
                        in
                     if uu____20804
                     then
                       let uv1 = FStar_Syntax_Free.uvars t1  in
                       let uv2 = FStar_Syntax_Free.uvars t2  in
                       let uu____20819 =
                         (FStar_Util.set_is_empty uv1) &&
                           (FStar_Util.set_is_empty uv2)
                          in
                       (if uu____20819
                        then
                          let guard =
                            let uu____20831 =
                              let uu____20832 = FStar_Syntax_Util.eq_tm t1 t2
                                 in
                              uu____20832 = FStar_Syntax_Util.Equal  in
                            if uu____20831
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____20836 = mk_eq2 env t1 t2  in
                               FStar_All.pipe_left
                                 (fun _0_86  ->
                                    FStar_Pervasives_Native.Some _0_86)
                                 uu____20836)
                             in
                          let uu____20839 = solve_prob orig guard [] wl  in
                          solve env uu____20839
                        else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2))
               | (uu____20842,FStar_Syntax_Syntax.Tm_app uu____20843) ->
                   let head1 =
                     let uu____20861 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____20861
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____20905 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____20905
                       FStar_Pervasives_Native.fst
                      in
                   ((let uu____20947 =
                       FStar_TypeChecker_Env.debug env
                         (FStar_Options.Other "RelCheck")
                        in
                     if uu____20947
                     then
                       let uu____20948 =
                         FStar_Util.string_of_int
                           problem.FStar_TypeChecker_Common.pid
                          in
                       let uu____20949 =
                         FStar_Syntax_Print.term_to_string head1  in
                       let uu____20950 =
                         FStar_Syntax_Print.term_to_string head2  in
                       FStar_Util.print3
                         ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                         uu____20948 uu____20949 uu____20950
                     else ());
                    (let uu____20952 =
                       (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          && wl.smt_ok)
                         &&
                         (problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ)
                        in
                     if uu____20952
                     then
                       let uv1 = FStar_Syntax_Free.uvars t1  in
                       let uv2 = FStar_Syntax_Free.uvars t2  in
                       let uu____20967 =
                         (FStar_Util.set_is_empty uv1) &&
                           (FStar_Util.set_is_empty uv2)
                          in
                       (if uu____20967
                        then
                          let guard =
                            let uu____20979 =
                              let uu____20980 = FStar_Syntax_Util.eq_tm t1 t2
                                 in
                              uu____20980 = FStar_Syntax_Util.Equal  in
                            if uu____20979
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____20984 = mk_eq2 env t1 t2  in
                               FStar_All.pipe_left
                                 (fun _0_87  ->
                                    FStar_Pervasives_Native.Some _0_87)
                                 uu____20984)
                             in
                          let uu____20987 = solve_prob orig guard [] wl  in
                          solve env uu____20987
                        else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                     else rigid_rigid_delta env orig wl head1 head2 t1 t2))
               | (FStar_Syntax_Syntax.Tm_let
                  uu____20990,FStar_Syntax_Syntax.Tm_let uu____20991) ->
                   let uu____21016 = FStar_Syntax_Util.term_eq t1 t2  in
                   if uu____21016
                   then
                     let uu____21017 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl  in
                     solve env uu____21017
                   else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
               | (FStar_Syntax_Syntax.Tm_let uu____21019,uu____21020) ->
                   let uu____21033 =
                     let uu____21038 =
                       let uu____21039 = FStar_Syntax_Print.tag_of_term t1
                          in
                       let uu____21040 = FStar_Syntax_Print.tag_of_term t2
                          in
                       let uu____21041 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____21042 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format4
                         "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                         uu____21039 uu____21040 uu____21041 uu____21042
                        in
                     (FStar_Errors.Fatal_UnificationNotWellFormed,
                       uu____21038)
                      in
                   FStar_Errors.raise_error uu____21033
                     t1.FStar_Syntax_Syntax.pos
               | (uu____21043,FStar_Syntax_Syntax.Tm_let uu____21044) ->
                   let uu____21057 =
                     let uu____21062 =
                       let uu____21063 = FStar_Syntax_Print.tag_of_term t1
                          in
                       let uu____21064 = FStar_Syntax_Print.tag_of_term t2
                          in
                       let uu____21065 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____21066 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format4
                         "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                         uu____21063 uu____21064 uu____21065 uu____21066
                        in
                     (FStar_Errors.Fatal_UnificationNotWellFormed,
                       uu____21062)
                      in
                   FStar_Errors.raise_error uu____21057
                     t1.FStar_Syntax_Syntax.pos
               | uu____21067 -> giveup env "head tag mismatch" orig)))

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
          let uu____21095 = p_scope orig  in
          mk_problem uu____21095 orig t1 rel t2 FStar_Pervasives_Native.None
            reason
           in
        let solve_eq c1_comp c2_comp =
          (let uu____21104 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____21104
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          if
            Prims.op_Negation
              (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name)
          then
            (let uu____21106 =
               let uu____21107 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____21108 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____21107 uu____21108
                in
             giveup env uu____21106 orig)
          else
            (let sub_probs =
               FStar_List.map2
                 (fun uu____21128  ->
                    fun uu____21129  ->
                      match (uu____21128, uu____21129) with
                      | ((a1,uu____21147),(a2,uu____21149)) ->
                          let uu____21158 =
                            sub_prob a1 FStar_TypeChecker_Common.EQ a2
                              "effect arg"
                             in
                          FStar_All.pipe_left
                            (fun _0_88  ->
                               FStar_TypeChecker_Common.TProb _0_88)
                            uu____21158)
                 c1_comp.FStar_Syntax_Syntax.effect_args
                 c2_comp.FStar_Syntax_Syntax.effect_args
                in
             let guard =
               let uu____21168 =
                 FStar_List.map
                   (fun p  ->
                      FStar_All.pipe_right (p_guard p)
                        FStar_Pervasives_Native.fst) sub_probs
                  in
               FStar_Syntax_Util.mk_conj_l uu____21168  in
             let wl1 =
               solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl  in
             solve env (attempt sub_probs wl1))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____21192 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____21199)::[] -> wp1
              | uu____21216 ->
                  let uu____21225 =
                    let uu____21226 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name)
                       in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____21226
                     in
                  failwith uu____21225
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____21234 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____21234]
              | x -> x  in
            let uu____21236 =
              let uu____21245 =
                let uu____21246 =
                  let uu____21247 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____21247 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____21246  in
              [uu____21245]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____21236;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____21248 = lift_c1 ()  in solve_eq uu____21248 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___115_21254  ->
                       match uu___115_21254 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____21255 -> false))
                in
             let uu____21256 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____21290)::uu____21291,(wp2,uu____21293)::uu____21294)
                   -> (wp1, wp2)
               | uu____21351 ->
                   let uu____21372 =
                     let uu____21377 =
                       let uu____21378 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____21379 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____21378 uu____21379
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____21377)
                      in
                   FStar_Errors.raise_error uu____21372
                     env.FStar_TypeChecker_Env.range
                in
             match uu____21256 with
             | (wpc1,wpc2) ->
                 let uu____21398 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____21398
                 then
                   let uu____21401 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____21401 wl
                 else
                   (let uu____21405 =
                      let uu____21412 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____21412  in
                    match uu____21405 with
                    | (c2_decl,qualifiers) ->
                        let uu____21433 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____21433
                        then
                          let c1_repr =
                            let uu____21437 =
                              let uu____21438 =
                                let uu____21439 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____21439  in
                              let uu____21440 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21438 uu____21440
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21437
                             in
                          let c2_repr =
                            let uu____21442 =
                              let uu____21443 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____21444 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____21443 uu____21444
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____21442
                             in
                          let prob =
                            let uu____21446 =
                              let uu____21451 =
                                let uu____21452 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____21453 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____21452
                                  uu____21453
                                 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____21451
                               in
                            FStar_TypeChecker_Common.TProb uu____21446  in
                          let wl1 =
                            let uu____21455 =
                              let uu____21458 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_Pervasives_Native.Some uu____21458  in
                            solve_prob orig uu____21455 [] wl  in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____21467 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21467
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____21470 =
                                     let uu____21473 =
                                       let uu____21474 =
                                         let uu____21489 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____21490 =
                                           let uu____21493 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____21494 =
                                             let uu____21497 =
                                               let uu____21498 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____21498
                                                in
                                             [uu____21497]  in
                                           uu____21493 :: uu____21494  in
                                         (uu____21489, uu____21490)  in
                                       FStar_Syntax_Syntax.Tm_app uu____21474
                                        in
                                     FStar_Syntax_Syntax.mk uu____21473  in
                                   uu____21470 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____21507 =
                                    let uu____21510 =
                                      let uu____21511 =
                                        let uu____21526 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____21527 =
                                          let uu____21530 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____21531 =
                                            let uu____21534 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____21535 =
                                              let uu____21538 =
                                                let uu____21539 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____21539
                                                 in
                                              [uu____21538]  in
                                            uu____21534 :: uu____21535  in
                                          uu____21530 :: uu____21531  in
                                        (uu____21526, uu____21527)  in
                                      FStar_Syntax_Syntax.Tm_app uu____21511
                                       in
                                    FStar_Syntax_Syntax.mk uu____21510  in
                                  uu____21507 FStar_Pervasives_Native.None r)
                              in
                           let base_prob =
                             let uu____21546 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type"
                                in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____21546
                              in
                           let wl1 =
                             let uu____21556 =
                               let uu____21559 =
                                 let uu____21562 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____21562 g  in
                               FStar_All.pipe_left
                                 (fun _0_90  ->
                                    FStar_Pervasives_Native.Some _0_90)
                                 uu____21559
                                in
                             solve_prob orig uu____21556 [] wl  in
                           solve env (attempt [base_prob] wl1))))
           in
        let uu____21575 = FStar_Util.physical_equality c1 c2  in
        if uu____21575
        then
          let uu____21576 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____21576
        else
          ((let uu____21579 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____21579
            then
              let uu____21580 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____21581 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____21580
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____21581
            else ());
           (let uu____21583 =
              let uu____21588 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____21589 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____21588, uu____21589)  in
            match uu____21583 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21593),FStar_Syntax_Syntax.Total
                    (t2,uu____21595)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21612 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21612 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21615,FStar_Syntax_Syntax.Total uu____21616) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21634),FStar_Syntax_Syntax.Total
                    (t2,uu____21636)) ->
                     let uu____21653 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21653 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21657),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21659)) ->
                     let uu____21676 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21676 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21680),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21682)) ->
                     let uu____21699 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21699 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21702,FStar_Syntax_Syntax.Comp uu____21703) ->
                     let uu____21712 =
                       let uu___164_21717 = problem  in
                       let uu____21722 =
                         let uu____21723 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21723
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___164_21717.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21722;
                         FStar_TypeChecker_Common.relation =
                           (uu___164_21717.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___164_21717.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___164_21717.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___164_21717.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___164_21717.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___164_21717.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___164_21717.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___164_21717.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21712 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21724,FStar_Syntax_Syntax.Comp uu____21725) ->
                     let uu____21734 =
                       let uu___164_21739 = problem  in
                       let uu____21744 =
                         let uu____21745 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21745
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___164_21739.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21744;
                         FStar_TypeChecker_Common.relation =
                           (uu___164_21739.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___164_21739.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___164_21739.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___164_21739.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___164_21739.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___164_21739.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___164_21739.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___164_21739.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21734 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21746,FStar_Syntax_Syntax.GTotal uu____21747) ->
                     let uu____21756 =
                       let uu___165_21761 = problem  in
                       let uu____21766 =
                         let uu____21767 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21767
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___165_21761.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___165_21761.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___165_21761.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21766;
                         FStar_TypeChecker_Common.element =
                           (uu___165_21761.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___165_21761.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___165_21761.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___165_21761.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___165_21761.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___165_21761.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21756 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21768,FStar_Syntax_Syntax.Total uu____21769) ->
                     let uu____21778 =
                       let uu___165_21783 = problem  in
                       let uu____21788 =
                         let uu____21789 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21789
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___165_21783.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___165_21783.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___165_21783.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21788;
                         FStar_TypeChecker_Common.element =
                           (uu___165_21783.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___165_21783.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___165_21783.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___165_21783.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___165_21783.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___165_21783.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21778 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21790,FStar_Syntax_Syntax.Comp uu____21791) ->
                     let uu____21792 =
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
                     if uu____21792
                     then
                       let uu____21793 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____21793 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21799 =
                            if
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21809 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____21810 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____21809, uu____21810))
                             in
                          match uu____21799 with
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
                           (let uu____21817 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____21817
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21819 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____21819 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21822 =
                                  let uu____21823 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____21824 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____21823 uu____21824
                                   in
                                giveup env uu____21822 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____21829 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21867  ->
              match uu____21867 with
              | (uu____21880,uu____21881,u,uu____21883,uu____21884,uu____21885)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____21829 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____21916 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____21916 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____21934 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21962  ->
                match uu____21962 with
                | (u1,u2) ->
                    let uu____21969 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____21970 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____21969 uu____21970))
         in
      FStar_All.pipe_right uu____21934 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21987,[])) -> "{}"
      | uu____22012 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____22029 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____22029
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____22032 =
              FStar_List.map
                (fun uu____22042  ->
                   match uu____22042 with
                   | (uu____22047,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____22032 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____22052 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____22052 imps
  
let new_t_problem :
  'Auu____22060 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term ->
            'Auu____22060 FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_Syntax_Syntax.term,'Auu____22060)
                  FStar_TypeChecker_Common.problem
  =
  fun env  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun loc  ->
              let reason =
                let uu____22094 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "ExplainRel")
                   in
                if uu____22094
                then
                  let uu____22095 =
                    FStar_TypeChecker_Normalize.term_to_string env lhs  in
                  let uu____22096 =
                    FStar_TypeChecker_Normalize.term_to_string env rhs  in
                  FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____22095
                    (rel_to_string rel) uu____22096
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
            let uu____22120 =
              let uu____22123 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left
                (fun _0_91  -> FStar_Pervasives_Native.Some _0_91)
                uu____22123
               in
            FStar_Syntax_Syntax.new_bv uu____22120 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____22132 =
              let uu____22135 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left
                (fun _0_92  -> FStar_Pervasives_Native.Some _0_92)
                uu____22135
               in
            let uu____22138 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____22132 uu____22138  in
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
          let uu____22168 = FStar_Options.eager_inference ()  in
          if uu____22168
          then
            let uu___166_22169 = probs  in
            {
              attempting = (uu___166_22169.attempting);
              wl_deferred = (uu___166_22169.wl_deferred);
              ctr = (uu___166_22169.ctr);
              defer_ok = false;
              smt_ok = (uu___166_22169.smt_ok);
              tcenv = (uu___166_22169.tcenv)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            ((let uu____22180 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____22180
              then
                let uu____22181 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____22181
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
          ((let uu____22195 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____22195
            then
              let uu____22196 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____22196
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____22200 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____22200
             then
               let uu____22201 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____22201
             else ());
            (let f2 =
               let uu____22204 =
                 let uu____22205 = FStar_Syntax_Util.unmeta f1  in
                 uu____22205.FStar_Syntax_Syntax.n  in
               match uu____22204 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____22209 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___167_22210 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___167_22210.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___167_22210.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___167_22210.FStar_TypeChecker_Env.implicits)
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
            let uu____22229 =
              let uu____22230 =
                let uu____22231 =
                  let uu____22232 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____22232
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____22231;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____22230  in
            FStar_All.pipe_left
              (fun _0_94  -> FStar_Pervasives_Native.Some _0_94) uu____22229
  
let with_guard_no_simp :
  'Auu____22259 .
    'Auu____22259 ->
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
            let uu____22279 =
              let uu____22280 =
                let uu____22281 =
                  FStar_All.pipe_right (p_guard prob)
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____22281
                  (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____22280;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____22279
  
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
          (let uu____22319 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____22319
           then
             let uu____22320 = FStar_Syntax_Print.term_to_string t1  in
             let uu____22321 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____22320
               uu____22321
           else ());
          (let prob =
             let uu____22324 =
               let uu____22329 = FStar_TypeChecker_Env.get_range env  in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____22329
                in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____22324
              in
           let g =
             let uu____22337 =
               let uu____22340 = singleton' env prob smt_ok  in
               solve_and_commit env uu____22340
                 (fun uu____22342  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob) uu____22337  in
           g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22360 = try_teq true env t1 t2  in
        match uu____22360 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____22364 = FStar_TypeChecker_Env.get_range env  in
              let uu____22365 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____22364 uu____22365);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____22372 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____22372
              then
                let uu____22373 = FStar_Syntax_Print.term_to_string t1  in
                let uu____22374 = FStar_Syntax_Print.term_to_string t2  in
                let uu____22375 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____22373
                  uu____22374 uu____22375
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
          let uu____22389 = FStar_TypeChecker_Env.get_range env  in
          let uu____22390 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____22389 uu____22390
  
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____22407 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22407
         then
           let uu____22408 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____22409 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____22408
             uu____22409
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB  in
         let prob =
           let uu____22414 =
             let uu____22419 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____22419 "sub_comp"
              in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____22414
            in
         let uu____22424 =
           let uu____22427 = singleton env prob  in
           solve_and_commit env uu____22427
             (fun uu____22429  -> FStar_Pervasives_Native.None)
            in
         FStar_All.pipe_left (with_guard env prob) uu____22424)
  
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
      fun uu____22458  ->
        match uu____22458 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22497 =
                 let uu____22502 =
                   let uu____22503 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____22504 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____22503 uu____22504
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____22502)  in
               let uu____22505 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____22497 uu____22505)
               in
            let equiv1 v1 v' =
              let uu____22513 =
                let uu____22518 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____22519 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____22518, uu____22519)  in
              match uu____22513 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22538 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22568 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____22568 with
                      | FStar_Syntax_Syntax.U_unif uu____22575 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22604  ->
                                    match uu____22604 with
                                    | (u,v') ->
                                        let uu____22613 = equiv1 v1 v'  in
                                        if uu____22613
                                        then
                                          let uu____22616 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____22616 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____22632 -> []))
               in
            let uu____22637 =
              let wl =
                let uu___168_22641 = empty_worklist env  in
                {
                  attempting = (uu___168_22641.attempting);
                  wl_deferred = (uu___168_22641.wl_deferred);
                  ctr = (uu___168_22641.ctr);
                  defer_ok = false;
                  smt_ok = (uu___168_22641.smt_ok);
                  tcenv = (uu___168_22641.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22659  ->
                      match uu____22659 with
                      | (lb,v1) ->
                          let uu____22666 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____22666 with
                           | USolved wl1 -> ()
                           | uu____22668 -> fail1 lb v1)))
               in
            let rec check_ineq uu____22676 =
              match uu____22676 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22685) -> true
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
                      uu____22708,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22710,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22721) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22728,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22736 -> false)
               in
            let uu____22741 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22756  ->
                      match uu____22756 with
                      | (u,v1) ->
                          let uu____22763 = check_ineq (u, v1)  in
                          if uu____22763
                          then true
                          else
                            ((let uu____22766 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____22766
                              then
                                let uu____22767 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____22768 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____22767
                                  uu____22768
                              else ());
                             false)))
               in
            if uu____22741
            then ()
            else
              ((let uu____22772 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____22772
                then
                  ((let uu____22774 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22774);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22784 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22784))
                else ());
               (let uu____22794 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____22794))
  
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
      let fail1 uu____22842 =
        match uu____22842 with
        | (d,s) ->
            let msg = explain env d s  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
              (p_loc d)
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____22856 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____22856
       then
         let uu____22857 = wl_to_string wl  in
         let uu____22858 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits)
            in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____22857 uu____22858
       else ());
      (let g1 =
         let uu____22873 = solve_and_commit env wl fail1  in
         match uu____22873 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___169_22886 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___169_22886.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___169_22886.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___169_22886.FStar_TypeChecker_Env.implicits)
             }
         | uu____22891 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___170_22895 = g1  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___170_22895.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___170_22895.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___170_22895.FStar_TypeChecker_Env.implicits)
        }))
  
let (last_proof_ns :
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (maybe_update_proof_ns : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns  in
    let uu____22921 = FStar_ST.op_Bang last_proof_ns  in
    match uu____22921 with
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
            let uu___171_23024 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___171_23024.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___171_23024.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___171_23024.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____23025 =
            let uu____23026 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____23026  in
          if uu____23025
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____23034 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____23035 =
                       let uu____23036 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____23036
                        in
                     FStar_Errors.diag uu____23034 uu____23035)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____23040 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____23041 =
                        let uu____23042 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____23042
                         in
                      FStar_Errors.diag uu____23040 uu____23041)
                   else ();
                   (let uu____23045 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in uu____23045 "discharge_guard'" env
                      vc1);
                   (let uu____23046 = check_trivial vc1  in
                    match uu____23046 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____23053 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____23054 =
                                let uu____23055 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____23055
                                 in
                              FStar_Errors.diag uu____23053 uu____23054)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____23060 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____23061 =
                                let uu____23062 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____23062
                                 in
                              FStar_Errors.diag uu____23060 uu____23061)
                           else ();
                           (let vcs =
                              let uu____23073 = FStar_Options.use_tactics ()
                                 in
                              if uu____23073
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____23092  ->
                                     (let uu____23094 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left
                                        FStar_Pervasives.ignore uu____23094);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____23096 =
                                   let uu____23103 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____23103)  in
                                 [uu____23096])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____23137  ->
                                    match uu____23137 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal
                                           in
                                        let uu____23148 = check_trivial goal1
                                           in
                                        (match uu____23148 with
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
                                                (let uu____23156 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____23157 =
                                                   let uu____23158 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   let uu____23159 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____23158 uu____23159
                                                    in
                                                 FStar_Errors.diag
                                                   uu____23156 uu____23157)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____23162 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____23163 =
                                                   let uu____23164 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____23164
                                                    in
                                                 FStar_Errors.diag
                                                   uu____23162 uu____23163)
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
      let uu____23174 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23174 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____23180 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____23180
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____23187 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____23187 with
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
          let uu____23206 = FStar_Syntax_Unionfind.find u  in
          match uu____23206 with
          | FStar_Pervasives_Native.None  -> true
          | uu____23209 -> false  in
        let rec until_fixpoint acc implicits =
          let uu____23227 = acc  in
          match uu____23227 with
          | (out,changed) ->
              (match implicits with
               | [] ->
                   if Prims.op_Negation changed
                   then out
                   else until_fixpoint ([], false) out
               | hd1::tl1 ->
                   let uu____23313 = hd1  in
                   (match uu____23313 with
                    | (uu____23326,env,u,tm,k,r) ->
                        let uu____23332 = unresolved u  in
                        if uu____23332
                        then until_fixpoint ((hd1 :: out), changed) tl1
                        else
                          (let tm1 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env tm
                              in
                           let env1 =
                             if forcelax
                             then
                               let uu___172_23362 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___172_23362.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___172_23362.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___172_23362.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___172_23362.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___172_23362.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___172_23362.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___172_23362.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___172_23362.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___172_23362.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___172_23362.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___172_23362.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___172_23362.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___172_23362.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___172_23362.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___172_23362.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___172_23362.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___172_23362.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___172_23362.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___172_23362.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___172_23362.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___172_23362.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___172_23362.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___172_23362.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___172_23362.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___172_23362.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___172_23362.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___172_23362.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___172_23362.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___172_23362.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___172_23362.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___172_23362.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___172_23362.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___172_23362.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___172_23362.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___172_23362.FStar_TypeChecker_Env.dep_graph)
                               }
                             else env  in
                           (let uu____23365 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "RelCheck")
                               in
                            if uu____23365
                            then
                              let uu____23366 =
                                FStar_Syntax_Print.uvar_to_string u  in
                              let uu____23367 =
                                FStar_Syntax_Print.term_to_string tm1  in
                              let uu____23368 =
                                FStar_Syntax_Print.term_to_string k  in
                              FStar_Util.print3
                                "Checking uvar %s resolved to %s at type %s\n"
                                uu____23366 uu____23367 uu____23368
                            else ());
                           (let g1 =
                              try
                                env1.FStar_TypeChecker_Env.check_type_of
                                  must_total env1 tm1 k
                              with
                              | e ->
                                  ((let uu____23379 =
                                      let uu____23388 =
                                        let uu____23395 =
                                          let uu____23396 =
                                            FStar_Syntax_Print.uvar_to_string
                                              u
                                             in
                                          let uu____23397 =
                                            FStar_TypeChecker_Normalize.term_to_string
                                              env1 tm1
                                             in
                                          FStar_Util.format2
                                            "Failed while checking implicit %s set to %s"
                                            uu____23396 uu____23397
                                           in
                                        (FStar_Errors.Error_BadImplicit,
                                          uu____23395, r)
                                         in
                                      [uu____23388]  in
                                    FStar_Errors.add_errors uu____23379);
                                   FStar_Exn.raise e)
                               in
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___175_23411 = g1  in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___175_23411.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___175_23411.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___175_23411.FStar_TypeChecker_Env.implicits)
                                }
                              else g1  in
                            let g' =
                              let uu____23414 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____23420  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true
                                 in
                              match uu____23414 with
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
        let uu___176_23448 = g  in
        let uu____23449 =
          until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___176_23448.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___176_23448.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            (uu___176_23448.FStar_TypeChecker_Env.univ_ineqs);
          FStar_TypeChecker_Env.implicits = uu____23449
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
        let uu____23503 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____23503 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23516 = discharge_guard env g1  in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____23516
      | (reason,uu____23518,uu____23519,e,t,r)::uu____23523 ->
          let uu____23550 =
            let uu____23555 =
              let uu____23556 = FStar_Syntax_Print.term_to_string t  in
              let uu____23557 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format2
                "Failed to resolve implicit argument of type '%s' introduced in %s"
                uu____23556 uu____23557
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____23555)
             in
          FStar_Errors.raise_error uu____23550 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___177_23564 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___177_23564.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___177_23564.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___177_23564.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____23587 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23587 with
      | FStar_Pervasives_Native.Some uu____23592 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23602 = try_teq false env t1 t2  in
        match uu____23602 with
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
        (let uu____23622 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23622
         then
           let uu____23623 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23624 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23623
             uu____23624
         else ());
        (let uu____23626 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____23626 with
         | (prob,x) ->
             let g =
               let uu____23642 =
                 let uu____23645 = singleton' env prob true  in
                 solve_and_commit env uu____23645
                   (fun uu____23647  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23642  in
             ((let uu____23657 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____23657
               then
                 let uu____23658 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____23659 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____23660 =
                   let uu____23661 = FStar_Util.must g  in
                   guard_to_string env uu____23661  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23658 uu____23659 uu____23660
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
        let uu____23689 = check_subtyping env t1 t2  in
        match uu____23689 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23708 =
              let uu____23709 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____23709 g  in
            FStar_Pervasives_Native.Some uu____23708
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23721 = check_subtyping env t1 t2  in
        match uu____23721 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23740 =
              let uu____23741 =
                let uu____23742 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____23742]  in
              close_guard env uu____23741 g  in
            FStar_Pervasives_Native.Some uu____23740
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23753 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23753
         then
           let uu____23754 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23755 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23754
             uu____23755
         else ());
        (let uu____23757 = new_t_prob env t1 FStar_TypeChecker_Common.SUB t2
            in
         match uu____23757 with
         | (prob,x) ->
             let g =
               let uu____23767 =
                 let uu____23770 = singleton' env prob false  in
                 solve_and_commit env uu____23770
                   (fun uu____23772  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23767  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23783 =
                      let uu____23784 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____23784]  in
                    close_guard env uu____23783 g1  in
                  discharge_guard_nosmt env g2))
  