open Prims
let guard_of_guard_formula :
  FStar_TypeChecker_Common.guard_formula -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    {
      FStar_TypeChecker_Env.guard_f = g;
      FStar_TypeChecker_Env.deferred = [];
      FStar_TypeChecker_Env.univ_ineqs = ([], []);
      FStar_TypeChecker_Env.implicits = []
    }
  
let guard_form :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Common.guard_formula =
  fun g  -> g.FStar_TypeChecker_Env.guard_f 
let is_trivial : FStar_TypeChecker_Env.guard_t -> Prims.bool =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Env.deferred = [];
        FStar_TypeChecker_Env.univ_ineqs = uu____23;
        FStar_TypeChecker_Env.implicits = uu____24;_} -> true
    | uu____38 -> false
  
let trivial_guard : FStar_TypeChecker_Env.guard_t =
  {
    FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial;
    FStar_TypeChecker_Env.deferred = [];
    FStar_TypeChecker_Env.univ_ineqs = ([], []);
    FStar_TypeChecker_Env.implicits = []
  } 
let abstract_guard :
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.guard_t option ->
      FStar_TypeChecker_Env.guard_t option
  =
  fun x  ->
    fun g  ->
      match g with
      | None  -> g
      | Some
          {
            FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
            FStar_TypeChecker_Env.deferred = uu____61;
            FStar_TypeChecker_Env.univ_ineqs = uu____62;
            FStar_TypeChecker_Env.implicits = uu____63;_}
          -> g
      | Some g1 ->
          let f =
            match g1.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.NonTrivial f -> f
            | uu____78 -> failwith "impossible"  in
          let uu____79 =
            let uu___135_80 = g1  in
            let uu____81 =
              let uu____82 =
                let uu____83 =
                  let uu____84 = FStar_Syntax_Syntax.mk_binder x  in
                  [uu____84]  in
                FStar_Syntax_Util.abs uu____83 f
                  (Some
                     (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
                 in
              FStar_All.pipe_left
                (fun _0_39  -> FStar_TypeChecker_Common.NonTrivial _0_39)
                uu____82
               in
            {
              FStar_TypeChecker_Env.guard_f = uu____81;
              FStar_TypeChecker_Env.deferred =
                (uu___135_80.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___135_80.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___135_80.FStar_TypeChecker_Env.implicits)
            }  in
          Some uu____79
  
let apply_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___136_94 = g  in
          let uu____95 =
            let uu____96 =
              let uu____97 =
                let uu____100 =
                  let uu____101 =
                    let uu____111 =
                      let uu____113 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____113]  in
                    (f, uu____111)  in
                  FStar_Syntax_Syntax.Tm_app uu____101  in
                FStar_Syntax_Syntax.mk uu____100  in
              uu____97
                (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_40  -> FStar_TypeChecker_Common.NonTrivial _0_40)
              uu____96
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____95;
            FStar_TypeChecker_Env.deferred =
              (uu___136_94.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___136_94.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___136_94.FStar_TypeChecker_Env.implicits)
          }
  
let map_guard :
  FStar_TypeChecker_Env.guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___137_137 = g  in
          let uu____138 =
            let uu____139 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____139  in
          {
            FStar_TypeChecker_Env.guard_f = uu____138;
            FStar_TypeChecker_Env.deferred =
              (uu___137_137.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___137_137.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___137_137.FStar_TypeChecker_Env.implicits)
          }
  
let trivial : FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____144 -> failwith "impossible"
  
let conj_guard_f :
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
          let uu____157 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____157
  
let check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula =
  fun t  ->
    let uu____162 =
      let uu____163 = FStar_Syntax_Util.unmeta t  in
      uu____163.FStar_Syntax_Syntax.n  in
    match uu____162 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____167 -> FStar_TypeChecker_Common.NonTrivial t
  
let imp_guard_f :
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
          let imp = FStar_Syntax_Util.mk_imp f1 f2  in check_trivial imp
  
let binop_guard :
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
        let uu____203 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____203;
          FStar_TypeChecker_Env.deferred =
            (FStar_List.append g1.FStar_TypeChecker_Env.deferred
               g2.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            ((FStar_List.append (fst g1.FStar_TypeChecker_Env.univ_ineqs)
                (fst g2.FStar_TypeChecker_Env.univ_ineqs)),
              (FStar_List.append (snd g1.FStar_TypeChecker_Env.univ_ineqs)
                 (snd g2.FStar_TypeChecker_Env.univ_ineqs)));
          FStar_TypeChecker_Env.implicits =
            (FStar_List.append g1.FStar_TypeChecker_Env.implicits
               g2.FStar_TypeChecker_Env.implicits)
        }
  
let conj_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  = fun g1  -> fun g2  -> binop_guard conj_guard_f g1 g2 
let imp_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  = fun g1  -> fun g2  -> binop_guard imp_guard_f g1 g2 
let close_guard_univs :
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
                       let uu____255 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____255
                       then f1
                       else FStar_Syntax_Util.mk_forall u (fst b) f1) us bs f
               in
            let uu___138_257 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___138_257.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___138_257.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___138_257.FStar_TypeChecker_Env.implicits)
            }
  
let close_forall :
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
               let uu____274 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____274
               then f1
               else
                 (let u =
                    env.FStar_TypeChecker_Env.universe_of env
                      (fst b).FStar_Syntax_Syntax.sort
                     in
                  FStar_Syntax_Util.mk_forall u (fst b) f1)) bs f
  
let close_guard :
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
            let uu___139_290 = g  in
            let uu____291 =
              let uu____292 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____292  in
            {
              FStar_TypeChecker_Env.guard_f = uu____291;
              FStar_TypeChecker_Env.deferred =
                (uu___139_290.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___139_290.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___139_290.FStar_TypeChecker_Env.implicits)
            }
  
let new_uvar :
  FStar_Range.range ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)
  =
  fun r  ->
    fun binders  ->
      fun k  ->
        let uv = FStar_Syntax_Unionfind.fresh ()  in
        match binders with
        | [] ->
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k))
                (Some (k.FStar_Syntax_Syntax.n)) r
               in
            (uv1, uv1)
        | uu____323 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder)
               in
            let k' =
              let uu____338 = FStar_Syntax_Syntax.mk_Total k  in
              FStar_Syntax_Util.arrow binders uu____338  in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                None r
               in
            let uu____350 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                (Some (k.FStar_Syntax_Syntax.n)) r
               in
            (uu____350, uv1)
  
let mk_eq2 :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____382 = FStar_Syntax_Util.type_u ()  in
        match uu____382 with
        | (t_type,u) ->
            let uu____387 =
              let uu____390 = FStar_TypeChecker_Env.all_binders env  in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____390 t_type  in
            (match uu____387 with
             | (tt,uu____392) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
  
type uvi =
  | TERM of ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) *
  FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let uu___is_TERM : uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____416 -> false
  
let __proj__TERM__item___0 :
  uvi ->
    ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) *
      FStar_Syntax_Syntax.term)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let uu___is_UNIV : uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____444 -> false
  
let __proj__UNIV__item___0 :
  uvi -> (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | UNIV _0 -> _0 
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list ;
  ctr: Prims.int ;
  defer_ok: Prims.bool ;
  smt_ok: Prims.bool ;
  tcenv: FStar_TypeChecker_Env.env }
let __proj__Mkworklist__item__attempting :
  worklist -> FStar_TypeChecker_Common.probs =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__attempting
  
let __proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list
  =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__wl_deferred
  
let __proj__Mkworklist__item__ctr : worklist -> Prims.int =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} -> __fname__ctr
  
let __proj__Mkworklist__item__defer_ok : worklist -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__defer_ok
  
let __proj__Mkworklist__item__smt_ok : worklist -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} ->
        __fname__smt_ok
  
let __proj__Mkworklist__item__tcenv : worklist -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;_} -> __fname__tcenv
  
type solution =
  | Success of FStar_TypeChecker_Common.deferred 
  | Failed of (FStar_TypeChecker_Common.prob * Prims.string) 
let uu___is_Success : solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____594 -> false
  
let __proj__Success__item___0 : solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0 
let uu___is_Failed : solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____610 -> false
  
let __proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let uu___is_COVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____629 -> false
  
let uu___is_CONTRAVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____634 -> false
  
let uu___is_INVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____639 -> false
  
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___107_657  ->
    match uu___107_657 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let term_to_string env t =
  let uu____673 =
    let uu____674 = FStar_Syntax_Subst.compress t  in
    uu____674.FStar_Syntax_Syntax.n  in
  match uu____673 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____691 = FStar_Syntax_Print.uvar_to_string u  in
      let uu____692 = FStar_Syntax_Print.term_to_string t1  in
      FStar_Util.format2 "(%s:%s)" uu____691 uu____692
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____695;
         FStar_Syntax_Syntax.pos = uu____696;
         FStar_Syntax_Syntax.vars = uu____697;_},args)
      ->
      let uu____725 = FStar_Syntax_Print.uvar_to_string u  in
      let uu____726 = FStar_Syntax_Print.term_to_string ty  in
      let uu____727 = FStar_Syntax_Print.args_to_string args  in
      FStar_Util.format3 "(%s:%s) %s" uu____725 uu____726 uu____727
  | uu____728 -> FStar_Syntax_Print.term_to_string t 
let prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___108_736  ->
      match uu___108_736 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____740 =
            let uu____742 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____743 =
              let uu____745 =
                term_to_string env p.FStar_TypeChecker_Common.lhs  in
              let uu____746 =
                let uu____748 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs
                   in
                let uu____749 =
                  let uu____751 =
                    let uu____753 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs  in
                    let uu____754 =
                      let uu____756 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs
                         in
                      let uu____757 =
                        let uu____759 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (fst p.FStar_TypeChecker_Common.logical_guard)
                           in
                        let uu____760 =
                          let uu____762 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t")
                             in
                          [uu____762]  in
                        uu____759 :: uu____760  in
                      uu____756 :: uu____757  in
                    uu____753 :: uu____754  in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____751
                   in
                uu____748 :: uu____749  in
              uu____745 :: uu____746  in
            uu____742 :: uu____743  in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____740
      | FStar_TypeChecker_Common.CProb p ->
          let uu____767 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____768 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____767
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____768
  
let uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___109_776  ->
      match uu___109_776 with
      | UNIV (u,t) ->
          let x =
            let uu____780 = FStar_Options.hide_uvar_nums ()  in
            if uu____780
            then "?"
            else
              (let uu____782 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____782 FStar_Util.string_of_int)
             in
          let uu____783 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____783
      | TERM ((u,uu____785),t) ->
          let x =
            let uu____790 = FStar_Options.hide_uvar_nums ()  in
            if uu____790
            then "?"
            else
              (let uu____792 = FStar_Syntax_Unionfind.uvar_id u  in
               FStar_All.pipe_right uu____792 FStar_Util.string_of_int)
             in
          let uu____793 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____793
  
let uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____804 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____804 (FStar_String.concat ", ")
  
let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____813 =
      let uu____815 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____815
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____813 (FStar_String.concat ", ")
  
let args_to_string args =
  let uu____835 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____843  ->
            match uu____843 with
            | (x,uu____847) -> FStar_Syntax_Print.term_to_string x))
     in
  FStar_All.pipe_right uu____835 (FStar_String.concat " ") 
let empty_worklist : FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____853 =
      let uu____854 = FStar_Options.eager_inference ()  in
      Prims.op_Negation uu____854  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____853;
      smt_ok = true;
      tcenv = env
    }
  
let singleton' :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.bool -> worklist
  =
  fun env  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___140_870 = empty_worklist env  in
        {
          attempting = [prob];
          wl_deferred = (uu___140_870.wl_deferred);
          ctr = (uu___140_870.ctr);
          defer_ok = (uu___140_870.defer_ok);
          smt_ok;
          tcenv = (uu___140_870.tcenv)
        }
  
let singleton :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true 
let wl_of_guard env g =
  let uu___141_900 = empty_worklist env  in
  let uu____901 = FStar_List.map FStar_Pervasives.snd g  in
  {
    attempting = uu____901;
    wl_deferred = (uu___141_900.wl_deferred);
    ctr = (uu___141_900.ctr);
    defer_ok = false;
    smt_ok = (uu___141_900.smt_ok);
    tcenv = (uu___141_900.tcenv)
  } 
let defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___142_916 = wl  in
        {
          attempting = (uu___142_916.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___142_916.ctr);
          defer_ok = (uu___142_916.defer_ok);
          smt_ok = (uu___142_916.smt_ok);
          tcenv = (uu___142_916.tcenv)
        }
  
let attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist =
  fun probs  ->
    fun wl  ->
      let uu___143_930 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___143_930.wl_deferred);
        ctr = (uu___143_930.ctr);
        defer_ok = (uu___143_930.defer_ok);
        smt_ok = (uu___143_930.smt_ok);
        tcenv = (uu___143_930.tcenv)
      }
  
let giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____944 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____944
         then
           let uu____945 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____945
         else ());
        Failed (prob, reason)
  
let invert_rel : FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___110_950  ->
    match uu___110_950 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert p =
  let uu___144_969 = p  in
  {
    FStar_TypeChecker_Common.pid =
      (uu___144_969.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___144_969.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___144_969.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___144_969.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___144_969.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___144_969.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___144_969.FStar_TypeChecker_Common.rank)
  } 
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p 
let maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___111_994  ->
    match uu___111_994 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.CProb _0_42)
  
let vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___112_1012  ->
      match uu___112_1012 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let p_pid : FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___113_1016  ->
    match uu___113_1016 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___114_1026  ->
    match uu___114_1026 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___115_1037  ->
    match uu___115_1037 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___116_1048  ->
    match uu___116_1048 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let p_guard :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun uu___117_1060  ->
    match uu___117_1060 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let p_scope : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___118_1072  ->
    match uu___118_1072 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
  
let p_invert : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___119_1082  ->
    match uu___119_1082 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) (invert p)
  
let is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____1097 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1097 = (Prims.parse_int "1")
  
let next_pid : Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1113  -> FStar_Util.incr ctr; FStar_ST.read ctr 
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1172 = next_pid ()  in
  let uu____1173 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0  in
  {
    FStar_TypeChecker_Common.pid = uu____1172;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1173;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  } 
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env  in
  let uu____1229 = next_pid ()  in
  let uu____1230 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0  in
  {
    FStar_TypeChecker_Common.pid = uu____1229;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1230;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  } 
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1279 = next_pid ()  in
  {
    FStar_TypeChecker_Common.pid = uu____1279;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = (p_guard orig);
    FStar_TypeChecker_Common.scope = (p_scope orig);
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  } 
let guard_on_element wl problem x phi =
  match problem.FStar_TypeChecker_Common.element with
  | None  ->
      let u =
        (wl.tcenv).FStar_TypeChecker_Env.universe_of wl.tcenv
          x.FStar_Syntax_Syntax.sort
         in
      FStar_Syntax_Util.mk_forall u x phi
  | Some e -> FStar_Syntax_Subst.subst [FStar_Syntax_Syntax.NT (x, e)] phi 
let explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____1339 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel")
           in
        if uu____1339
        then
          let uu____1340 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____1341 = prob_to_string env d  in
          let uu____1342 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1340 uu____1341 uu____1342 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1347 -> failwith "impossible"  in
           let uu____1348 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1356 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____1357 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____1356, uu____1357)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1361 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____1362 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____1361, uu____1362)
              in
           match uu____1348 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let commit : uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___120_1372  ->
            match uu___120_1372 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1378 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1380),t) -> FStar_Syntax_Util.set_uvar u t))
  
let find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___121_1395  ->
           match uu___121_1395 with
           | UNIV uu____1397 -> None
           | TERM ((u,uu____1401),t) ->
               let uu____1405 = FStar_Syntax_Unionfind.equiv uv u  in
               if uu____1405 then Some t else None)
  
let find_univ_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___122_1419  ->
           match uu___122_1419 with
           | UNIV (u',t) ->
               let uu____1423 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____1423 then Some t else None
           | uu____1426 -> None)
  
let whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1435 =
        let uu____1436 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1436
         in
      FStar_Syntax_Subst.compress uu____1435
  
let sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1445 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____1445
  
let norm_arg env t =
  let uu____1467 = sn env (fst t)  in (uu____1467, (snd t)) 
let sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1486  ->
              match uu____1486 with
              | (x,imp) ->
                  let uu____1493 =
                    let uu___145_1494 = x  in
                    let uu____1495 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___145_1494.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___145_1494.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1495
                    }  in
                  (uu____1493, imp)))
  
let norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1512 = aux u3  in FStar_Syntax_Syntax.U_succ uu____1512
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1515 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____1515
        | uu____1517 -> u2  in
      let uu____1518 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1518
  
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0 
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1634 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           match uu____1634 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1646;
               FStar_Syntax_Syntax.pos = uu____1647;
               FStar_Syntax_Syntax.vars = uu____1648;_} ->
               ((x1.FStar_Syntax_Syntax.sort), (Some (x1, phi1)))
           | tt ->
               let uu____1669 =
                 let uu____1670 = FStar_Syntax_Print.term_to_string tt  in
                 let uu____1671 = FStar_Syntax_Print.tag_of_term tt  in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1670
                   uu____1671
                  in
               failwith uu____1669)
    | FStar_Syntax_Syntax.Tm_uinst uu____1681 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           let uu____1708 =
             let uu____1709 = FStar_Syntax_Subst.compress t1'  in
             uu____1709.FStar_Syntax_Syntax.n  in
           match uu____1708 with
           | FStar_Syntax_Syntax.Tm_refine uu____1721 -> aux true t1'
           | uu____1726 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_fvar uu____1738 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           let uu____1761 =
             let uu____1762 = FStar_Syntax_Subst.compress t1'  in
             uu____1762.FStar_Syntax_Syntax.n  in
           match uu____1761 with
           | FStar_Syntax_Syntax.Tm_refine uu____1774 -> aux true t1'
           | uu____1779 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_app uu____1791 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           let uu____1823 =
             let uu____1824 = FStar_Syntax_Subst.compress t1'  in
             uu____1824.FStar_Syntax_Syntax.n  in
           match uu____1823 with
           | FStar_Syntax_Syntax.Tm_refine uu____1836 -> aux true t1'
           | uu____1841 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_type uu____1853 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_constant uu____1865 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_name uu____1877 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_bvar uu____1889 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_arrow uu____1901 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_abs uu____1920 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_uvar uu____1941 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_let uu____1961 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_match uu____1980 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_meta uu____2007 ->
        let uu____2012 =
          let uu____2013 = FStar_Syntax_Print.term_to_string t11  in
          let uu____2014 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2013
            uu____2014
           in
        failwith uu____2012
    | FStar_Syntax_Syntax.Tm_ascribed uu____2024 ->
        let uu____2042 =
          let uu____2043 = FStar_Syntax_Print.term_to_string t11  in
          let uu____2044 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2043
            uu____2044
           in
        failwith uu____2042
    | FStar_Syntax_Syntax.Tm_delayed uu____2054 ->
        let uu____2069 =
          let uu____2070 = FStar_Syntax_Print.term_to_string t11  in
          let uu____2071 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2070
            uu____2071
           in
        failwith uu____2069
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____2081 =
          let uu____2082 = FStar_Syntax_Print.term_to_string t11  in
          let uu____2083 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____2082
            uu____2083
           in
        failwith uu____2081
     in
  let uu____2093 = whnf env t1  in aux false uu____2093 
let unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____2104 =
        let uu____2114 = empty_worklist env  in
        base_and_refinement env uu____2114 t  in
      FStar_All.pipe_right uu____2104 FStar_Pervasives.fst
  
let trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____2139 = FStar_Syntax_Syntax.null_bv t  in
    (uu____2139, FStar_Syntax_Util.t_true)
  
let as_refinement env wl t =
  let uu____2163 = base_and_refinement env wl t  in
  match uu____2163 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
  
let force_refinement uu____2224 =
  match uu____2224 with
  | (t_base,refopt) ->
      let uu____2238 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base  in
      (match uu____2238 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
  
let wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___123_2264  ->
      match uu___123_2264 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2268 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____2269 =
            let uu____2270 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
            FStar_Syntax_Print.term_to_string uu____2270  in
          let uu____2271 =
            let uu____2272 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
            FStar_Syntax_Print.term_to_string uu____2272  in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2268 uu____2269
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2271
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2276 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____2277 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____2278 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2276 uu____2277
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2278
  
let wl_to_string : worklist -> Prims.string =
  fun wl  ->
    let uu____2283 =
      let uu____2285 =
        let uu____2287 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2297  ->
                  match uu____2297 with | (uu____2301,uu____2302,x) -> x))
           in
        FStar_List.append wl.attempting uu____2287  in
      FStar_List.map (wl_prob_to_string wl) uu____2285  in
    FStar_All.pipe_right uu____2283 (FStar_String.concat "\n\t")
  
let u_abs :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2323 =
          let uu____2333 =
            let uu____2334 = FStar_Syntax_Subst.compress k  in
            uu____2334.FStar_Syntax_Syntax.n  in
          match uu____2333 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2379 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____2379)
              else
                (let uu____2393 = FStar_Syntax_Util.abs_formals t  in
                 match uu____2393 with
                 | (ys',t1,uu____2409) ->
                     let uu____2412 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____2412))
          | uu____2433 ->
              let uu____2434 =
                let uu____2440 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____2440)  in
              ((ys, t), uu____2434)
           in
        match uu____2323 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Syntax_Util.mk_residual_comp
                      FStar_Syntax_Const.effect_Tot_lid None []))
            else
              (let c1 =
                 let uu____2492 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____2492 c  in
               FStar_Syntax_Util.abs ys1 t1
                 (Some (FStar_Syntax_Util.residual_comp_of_comp c1)))
  
let solve_prob' :
  Prims.bool ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term option ->
        uvi Prims.list -> worklist -> worklist
  =
  fun resolve_ok  ->
    fun prob  ->
      fun logical_guard  ->
        fun uvis  ->
          fun wl  ->
            let phi =
              match logical_guard with
              | None  -> FStar_Syntax_Util.t_true
              | Some phi -> phi  in
            let uu____2520 = p_guard prob  in
            match uu____2520 with
            | (uu____2523,uv) ->
                ((let uu____2526 =
                    let uu____2527 = FStar_Syntax_Subst.compress uv  in
                    uu____2527.FStar_Syntax_Syntax.n  in
                  match uu____2526 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob  in
                      let phi1 = u_abs k bs phi  in
                      ((let uu____2547 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel")
                           in
                        if uu____2547
                        then
                          let uu____2548 =
                            FStar_Util.string_of_int (p_pid prob)  in
                          let uu____2549 =
                            FStar_Syntax_Print.term_to_string uv  in
                          let uu____2550 =
                            FStar_Syntax_Print.term_to_string phi1  in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2548
                            uu____2549 uu____2550
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2552 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___146_2555 = wl  in
                  {
                    attempting = (uu___146_2555.attempting);
                    wl_deferred = (uu___146_2555.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___146_2555.defer_ok);
                    smt_ok = (uu___146_2555.smt_ok);
                    tcenv = (uu___146_2555.tcenv)
                  }))
  
let extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2571 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck")
            in
         if uu____2571
         then
           let uu____2572 = FStar_Util.string_of_int pid  in
           let uu____2573 =
             let uu____2574 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____2574 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2572 uu____2573
         else ());
        commit sol;
        (let uu___147_2579 = wl  in
         {
           attempting = (uu___147_2579.attempting);
           wl_deferred = (uu___147_2579.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___147_2579.defer_ok);
           smt_ok = (uu___147_2579.smt_ok);
           tcenv = (uu___147_2579.tcenv)
         })
  
let solve_prob :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term option -> uvi Prims.list -> worklist -> worklist
  =
  fun prob  ->
    fun logical_guard  ->
      fun uvis  ->
        fun wl  ->
          let conj_guard1 t g =
            match (t, g) with
            | (uu____2612,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2620 = FStar_Syntax_Util.mk_conj t1 f  in
                Some uu____2620
             in
          (let uu____2626 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck")
              in
           if uu____2626
           then
             let uu____2627 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____2628 =
               let uu____2629 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____2629 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2627 uu____2628
           else ());
          solve_prob' false prob logical_guard uvis wl
  
let rec occurs wl uk t =
  let uu____2658 =
    let uu____2662 = FStar_Syntax_Free.uvars t  in
    FStar_All.pipe_right uu____2662 FStar_Util.set_elements  in
  FStar_All.pipe_right uu____2658
    (FStar_Util.for_some
       (fun uu____2679  ->
          match uu____2679 with
          | (uv,uu____2683) -> FStar_Syntax_Unionfind.equiv uv (fst uk)))
  
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2722 = occurs wl uk t  in Prims.op_Negation uu____2722  in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2727 =
         let uu____2728 = FStar_Syntax_Print.uvar_to_string (fst uk)  in
         let uu____2729 = FStar_Syntax_Print.term_to_string t  in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2728 uu____2729
          in
       Some uu____2727)
     in
  (occurs_ok, msg) 
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t  in
  let uu____2784 = occurs_check env wl uk t  in
  match uu____2784 with
  | (occurs_ok,msg) ->
      let uu____2801 = FStar_Util.set_is_subset_of fvs_t fvs  in
      (occurs_ok, uu____2801, (msg, fvs, fvs_t))
  
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (fst x) out)
         FStar_Syntax_Syntax.no_names)
     in
  let v1_set = as_set1 v1  in
  let uu____2869 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2893  ->
            fun uu____2894  ->
              match (uu____2893, uu____2894) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2937 =
                    let uu____2938 = FStar_Util.set_mem x v1_set  in
                    FStar_All.pipe_left Prims.op_Negation uu____2938  in
                  if uu____2937
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort  in
                     let uu____2952 =
                       FStar_Util.set_is_subset_of fvs isect_set  in
                     if uu____2952
                     then
                       let uu____2959 = FStar_Util.set_add x isect_set  in
                       (((x, imp) :: isect), uu____2959)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names))
     in
  match uu____2869 with | (isect,uu____2981) -> FStar_List.rev isect 
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____3038  ->
          fun uu____3039  ->
            match (uu____3038, uu____3039) with
            | ((a,uu____3049),(b,uu____3051)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg  in
  match (fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____3100 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____3106  ->
                match uu____3106 with
                | (b,uu____3110) -> FStar_Syntax_Syntax.bv_eq a b))
         in
      if uu____3100 then None else Some (a, (snd hd1))
  | uu____3119 -> None 
let rec pat_vars :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list ->
        FStar_Syntax_Syntax.binders option
  =
  fun env  ->
    fun seen  ->
      fun args  ->
        match args with
        | [] -> Some (FStar_List.rev seen)
        | hd1::rest ->
            let uu____3165 = pat_var_opt env seen hd1  in
            (match uu____3165 with
             | None  ->
                 ((let uu____3173 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel")
                      in
                   if uu____3173
                   then
                     let uu____3174 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (fst hd1)
                        in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____3174
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
  
let is_flex : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3187 =
      let uu____3188 = FStar_Syntax_Subst.compress t  in
      uu____3188.FStar_Syntax_Syntax.n  in
    match uu____3187 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3191 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3200;
           FStar_Syntax_Syntax.tk = uu____3201;
           FStar_Syntax_Syntax.pos = uu____3202;
           FStar_Syntax_Syntax.vars = uu____3203;_},uu____3204)
        -> true
    | uu____3227 -> false
  
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____3291;
         FStar_Syntax_Syntax.pos = uu____3292;
         FStar_Syntax_Syntax.vars = uu____3293;_},args)
      -> (t, uv, k, args)
  | uu____3334 -> failwith "Not a flex-uvar" 
let destruct_flex_pattern env t =
  let uu____3391 = destruct_flex_t t  in
  match uu____3391 with
  | (t1,uv,k,args) ->
      let uu____3459 = pat_vars env [] args  in
      (match uu____3459 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3515 -> ((t1, uv, k, args), None))
  
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth option *
  FStar_Syntax_Syntax.delta_depth option) 
  | HeadMatch 
  | FullMatch 
let uu___is_MisMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3565 -> false
  
let __proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth option * FStar_Syntax_Syntax.delta_depth
      option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let uu___is_HeadMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3590 -> false
  
let uu___is_FullMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3595 -> false
  
let head_match : match_result -> match_result =
  fun uu___124_3599  ->
    match uu___124_3599 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3608 -> HeadMatch
  
let fv_delta_depth :
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3623 ->
          let uu____3624 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____3624 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3634 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
  
let rec delta_depth_of_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____3650 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3656 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> None
      | FStar_Syntax_Syntax.Tm_bvar uu____3672 -> None
      | FStar_Syntax_Syntax.Tm_name uu____3673 -> None
      | FStar_Syntax_Syntax.Tm_uvar uu____3674 -> None
      | FStar_Syntax_Syntax.Tm_let uu____3683 -> None
      | FStar_Syntax_Syntax.Tm_match uu____3691 -> None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3708) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3714,uu____3715) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3745) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3760;
             FStar_Syntax_Syntax.index = uu____3761;
             FStar_Syntax_Syntax.sort = t2;_},uu____3763)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3770 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3771 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3772 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3780 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3791 = fv_delta_depth env fv  in Some uu____3791
  
let rec head_matches :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> match_result
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
            else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____3813 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____3813
            then FullMatch
            else
              (let uu____3815 =
                 let uu____3820 =
                   let uu____3822 = fv_delta_depth env f  in Some uu____3822
                    in
                 let uu____3823 =
                   let uu____3825 = fv_delta_depth env g  in Some uu____3825
                    in
                 (uu____3820, uu____3823)  in
               MisMatch uu____3815)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3829),FStar_Syntax_Syntax.Tm_uinst (g,uu____3831)) ->
            let uu____3840 = head_matches env f g  in
            FStar_All.pipe_right uu____3840 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3847),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3849)) ->
            let uu____3874 = FStar_Syntax_Unionfind.equiv uv uv'  in
            if uu____3874 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3879),FStar_Syntax_Syntax.Tm_refine (y,uu____3881)) ->
            let uu____3890 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____3890 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3892),uu____3893) ->
            let uu____3898 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____3898 head_match
        | (uu____3899,FStar_Syntax_Syntax.Tm_refine (x,uu____3901)) ->
            let uu____3906 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____3906 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____3907,FStar_Syntax_Syntax.Tm_type
           uu____3908) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____3909,FStar_Syntax_Syntax.Tm_arrow uu____3910) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3926),FStar_Syntax_Syntax.Tm_app (head',uu____3928))
            ->
            let uu____3957 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____3957 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3959),uu____3960) ->
            let uu____3975 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____3975 head_match
        | (uu____3976,FStar_Syntax_Syntax.Tm_app (head1,uu____3978)) ->
            let uu____3993 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____3993 head_match
        | uu____3994 ->
            let uu____3997 =
              let uu____4002 = delta_depth_of_term env t11  in
              let uu____4004 = delta_depth_of_term env t21  in
              (uu____4002, uu____4004)  in
            MisMatch uu____3997
  
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____4045 = FStar_Syntax_Util.head_and_args t  in
    match uu____4045 with
    | (head1,uu____4057) ->
        let uu____4072 =
          let uu____4073 = FStar_Syntax_Util.un_uinst head1  in
          uu____4073.FStar_Syntax_Syntax.n  in
        (match uu____4072 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____4078 =
               let uu____4079 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               FStar_All.pipe_right uu____4079 FStar_Option.isSome  in
             if uu____4078
             then
               let uu____4093 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t
                  in
               FStar_All.pipe_right uu____4093 (fun _0_45  -> Some _0_45)
             else None
         | uu____4096 -> None)
     in
  let success d r t11 t21 =
    (r, (if d > (Prims.parse_int "0") then Some (t11, t21) else None))  in
  let fail r = (r, None)  in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21  in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),uu____4164) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4174 =
             let uu____4179 = maybe_inline t11  in
             let uu____4181 = maybe_inline t21  in (uu____4179, uu____4181)
              in
           match uu____4174 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (uu____4202,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4212 =
             let uu____4217 = maybe_inline t11  in
             let uu____4219 = maybe_inline t21  in (uu____4217, uu____4219)
              in
           match uu____4212 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____4244 = FStar_TypeChecker_Common.decr_delta_depth d1  in
        (match uu____4244 with
         | None  -> fail r
         | Some d ->
             let t12 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d;
                 FStar_TypeChecker_Normalize.WHNF] env wl t11
                in
             let t22 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21
                in
             aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) ->
        let d1_greater_than_d2 =
          FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
        let uu____4259 =
          if d1_greater_than_d2
          then
            let t1' =
              normalize_refinement
                [FStar_TypeChecker_Normalize.UnfoldUntil d2;
                FStar_TypeChecker_Normalize.WHNF] env wl t11
               in
            (t1', t21)
          else
            (let t2' =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21
                in
             (t11, t2'))
           in
        (match uu____4259 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4274 -> fail r
    | uu____4279 -> success n_delta r t11 t21  in
  aux true (Prims.parse_int "0") t1 t2 
type tc =
  | T of (FStar_Syntax_Syntax.term *
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  
  | C of FStar_Syntax_Syntax.comp 
let uu___is_T : tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4309 -> false 
let __proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term *
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0 
let uu___is_C : tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4341 -> false 
let __proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list
let generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4359 = FStar_Syntax_Util.type_u ()  in
      match uu____4359 with
      | (t,uu____4363) ->
          let uu____4364 = new_uvar r binders t  in fst uu____4364
  
let kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4375 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____4375 FStar_Pervasives.fst
  
let rec decompose :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      ((tc Prims.list -> FStar_Syntax_Syntax.term) *
        (FStar_Syntax_Syntax.term -> Prims.bool) *
        (FStar_Syntax_Syntax.binder option * variance * tc) Prims.list)
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let matches t' =
        let uu____4419 = head_matches env t1 t'  in
        match uu____4419 with
        | MisMatch uu____4420 -> false
        | uu____4425 -> true  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4485,imp),T (t2,uu____4488)) -> (t2, imp)
                     | uu____4505 -> failwith "Bad reconstruction") args
                args'
               in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              None t1.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4545  ->
                    match uu____4545 with
                    | (t2,uu____4553) ->
                        (None, INVARIANT, (T (t2, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____4583 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____4583 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4636))::tcs2) ->
                       aux
                         (((let uu___148_4658 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_4658.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_4658.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4668 -> failwith "Bad reconstruction"  in
                 aux [] bs1 tcs  in
               let rec decompose1 out uu___125_4699 =
                 match uu___125_4699 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest
                  in
               let uu____4762 = decompose1 [] bs1  in
               (rebuild, matches, uu____4762))
      | uu____4790 ->
          let rebuild uu___126_4795 =
            match uu___126_4795 with
            | [] -> t1
            | uu____4797 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t2  -> true)), [])
  
let un_T : tc -> FStar_Syntax_Syntax.term =
  fun uu___127_4817  ->
    match uu___127_4817 with
    | T (t,uu____4819) -> t
    | uu____4828 -> failwith "Impossible"
  
let arg_of_tc : tc -> FStar_Syntax_Syntax.arg =
  fun uu___128_4832  ->
    match uu___128_4832 with
    | T (t,uu____4834) -> FStar_Syntax_Syntax.as_arg t
    | uu____4843 -> failwith "Impossible"
  
let imitation_sub_probs :
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.args ->
          (FStar_Syntax_Syntax.binder option * variance * tc) Prims.list ->
            (FStar_TypeChecker_Common.prob Prims.list * tc Prims.list *
              FStar_Syntax_Syntax.formula)
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
              | (uu____4917,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r  in
                  let uu____4936 = new_uvar r scope1 k  in
                  (match uu____4936 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4948 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args)) None r
                          in
                       let uu____4963 =
                         let uu____4964 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm"
                            in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____4964
                          in
                       ((T (gi_xs, mk_kind)), uu____4963))
              | (uu____4973,uu____4974,C uu____4975) -> failwith "impos"  in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____5062 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____5073;
                         FStar_Syntax_Syntax.pos = uu____5074;
                         FStar_Syntax_Syntax.vars = uu____5075;_})
                        ->
                        let uu____5090 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____5090 with
                         | (T (gi_xs,uu____5106),prob) ->
                             let uu____5116 =
                               let uu____5117 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____5117
                                in
                             (uu____5116, [prob])
                         | uu____5119 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____5129;
                         FStar_Syntax_Syntax.pos = uu____5130;
                         FStar_Syntax_Syntax.vars = uu____5131;_})
                        ->
                        let uu____5146 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____5146 with
                         | (T (gi_xs,uu____5162),prob) ->
                             let uu____5172 =
                               let uu____5173 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                                  in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____5173
                                in
                             (uu____5172, [prob])
                         | uu____5175 -> failwith "impossible")
                    | (uu____5181,uu____5182,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____5184;
                         FStar_Syntax_Syntax.pos = uu____5185;
                         FStar_Syntax_Syntax.vars = uu____5186;_})
                        ->
                        let components =
                          FStar_All.pipe_right
                            c.FStar_Syntax_Syntax.effect_args
                            (FStar_List.map
                               (fun t  ->
                                  (None, INVARIANT,
                                    (T ((fst t), generic_kind)))))
                           in
                        let components1 =
                          (None, COVARIANT,
                            (T
                               ((c.FStar_Syntax_Syntax.result_typ),
                                 kind_type)))
                          :: components  in
                        let uu____5260 =
                          let uu____5265 =
                            FStar_List.map (sub_prob scope1 args) components1
                             in
                          FStar_All.pipe_right uu____5265 FStar_List.unzip
                           in
                        (match uu____5260 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5294 =
                                 let uu____5295 =
                                   let uu____5298 = FStar_List.hd tcs  in
                                   FStar_All.pipe_right uu____5298 un_T  in
                                 let uu____5299 =
                                   let uu____5305 = FStar_List.tl tcs  in
                                   FStar_All.pipe_right uu____5305
                                     (FStar_List.map arg_of_tc)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5295;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5299;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 }  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5294
                                in
                             ((C gi_xs), sub_probs))
                    | uu____5310 ->
                        let uu____5317 = sub_prob scope1 args q  in
                        (match uu____5317 with
                         | (ktec,prob) -> (ktec, [prob]))
                     in
                  (match uu____5062 with
                   | (tc,probs) ->
                       let uu____5335 =
                         match q with
                         | (Some b,uu____5361,uu____5362) ->
                             let uu____5370 =
                               let uu____5374 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b
                                  in
                               uu____5374 :: args  in
                             ((Some b), (b :: scope1), uu____5370)
                         | uu____5392 -> (None, scope1, args)  in
                       (match uu____5335 with
                        | (bopt,scope2,args1) ->
                            let uu____5435 = aux scope2 args1 qs2  in
                            (match uu____5435 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____5456 =
                                         let uu____5458 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst))
                                            in
                                         f :: uu____5458  in
                                       FStar_Syntax_Util.mk_conj_l uu____5456
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (fst b).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____5471 =
                                         let uu____5473 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (fst b) f
                                            in
                                         let uu____5474 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst))
                                            in
                                         uu____5473 :: uu____5474  in
                                       FStar_Syntax_Util.mk_conj_l uu____5471
                                    in
                                 ((FStar_List.append probs sub_probs), (tc ::
                                   tcs), f1))))
               in
            aux scope ps qs
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.uvar *
    FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.args)
type im_or_proj_t =
  (((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) *
    FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) *
    FStar_Syntax_Syntax.arg Prims.list *
    ((tc Prims.list -> FStar_Syntax_Syntax.typ) *
    (FStar_Syntax_Syntax.typ -> Prims.bool) * (FStar_Syntax_Syntax.binder
    option * variance * tc) Prims.list))
let rigid_rigid : Prims.int = (Prims.parse_int "0") 
let flex_rigid_eq : Prims.int = (Prims.parse_int "1") 
let flex_refine_inner : Prims.int = (Prims.parse_int "2") 
let flex_refine : Prims.int = (Prims.parse_int "3") 
let flex_rigid : Prims.int = (Prims.parse_int "4") 
let rigid_flex : Prims.int = (Prims.parse_int "5") 
let refine_flex : Prims.int = (Prims.parse_int "6") 
let flex_flex : Prims.int = (Prims.parse_int "7") 
let compress_tprob wl p =
  let uu___149_5530 = p  in
  let uu____5533 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
  let uu____5534 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
  {
    FStar_TypeChecker_Common.pid =
      (uu___149_5530.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5533;
    FStar_TypeChecker_Common.relation =
      (uu___149_5530.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5534;
    FStar_TypeChecker_Common.element =
      (uu___149_5530.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___149_5530.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___149_5530.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___149_5530.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___149_5530.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___149_5530.FStar_TypeChecker_Common.rank)
  } 
let compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5546 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____5546
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____5551 -> p
  
let rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int * FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5567 = compress_prob wl pr  in
        FStar_All.pipe_right uu____5567 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5573 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____5573 with
           | (lh,uu____5586) ->
               let uu____5601 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____5601 with
                | (rh,uu____5614) ->
                    let uu____5629 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5638,FStar_Syntax_Syntax.Tm_uvar uu____5639)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5658,uu____5659)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5670,FStar_Syntax_Syntax.Tm_uvar uu____5671)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5682,uu____5683)
                          ->
                          let uu____5692 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____5692 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5732 ->
                                    let rank =
                                      let uu____5739 = is_top_level_prob prob
                                         in
                                      if uu____5739
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____5741 =
                                      let uu___150_5744 = tp  in
                                      let uu____5747 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___150_5744.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___150_5744.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___150_5744.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5747;
                                        FStar_TypeChecker_Common.element =
                                          (uu___150_5744.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___150_5744.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___150_5744.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___150_5744.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___150_5744.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___150_5744.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____5741)))
                      | (uu____5757,FStar_Syntax_Syntax.Tm_uvar uu____5758)
                          ->
                          let uu____5767 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____5767 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5807 ->
                                    let uu____5813 =
                                      let uu___151_5818 = tp  in
                                      let uu____5821 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___151_5818.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5821;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___151_5818.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___151_5818.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___151_5818.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___151_5818.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___151_5818.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___151_5818.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___151_5818.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___151_5818.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____5813)))
                      | (uu____5837,uu____5838) -> (rigid_rigid, tp)  in
                    (match uu____5629 with
                     | (rank,tp1) ->
                         let uu____5849 =
                           FStar_All.pipe_right
                             (let uu___152_5852 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___152_5852.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___152_5852.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___152_5852.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___152_5852.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___152_5852.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___152_5852.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___152_5852.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___152_5852.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___152_5852.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50)
                            in
                         (rank, uu____5849))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5858 =
            FStar_All.pipe_right
              (let uu___153_5861 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___153_5861.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___153_5861.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___153_5861.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___153_5861.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___153_5861.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___153_5861.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___153_5861.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___153_5861.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___153_5861.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51)
             in
          (rigid_rigid, uu____5858)
  
let next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob option * FStar_TypeChecker_Common.prob
      Prims.list * Prims.int)
  =
  fun wl  ->
    let rec aux uu____5894 probs =
      match uu____5894 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5924 = rank wl hd1  in
               (match uu____5924 with
                | (rank1,hd2) ->
                    if rank1 <= flex_rigid_eq
                    then
                      (match min1 with
                       | None  ->
                           ((Some hd2), (FStar_List.append out tl1), rank1)
                       | Some m ->
                           ((Some hd2), (FStar_List.append out (m :: tl1)),
                             rank1))
                    else
                      if rank1 < min_rank
                      then
                        (match min1 with
                         | None  -> aux (rank1, (Some hd2), out) tl1
                         | Some m -> aux (rank1, (Some hd2), (m :: out)) tl1)
                      else aux (min_rank, min1, (hd2 :: out)) tl1))
       in
    aux ((flex_flex + (Prims.parse_int "1")), None, []) wl.attempting
  
let is_flex_rigid : Prims.int -> Prims.bool =
  fun rank1  -> (flex_refine_inner <= rank1) && (rank1 <= flex_rigid) 
let is_rigid_flex : Prims.int -> Prims.bool =
  fun rank1  -> (rigid_flex <= rank1) && (rank1 <= refine_flex) 
type univ_eq_sol =
  | UDeferred of worklist 
  | USolved of worklist 
  | UFailed of Prims.string 
let uu___is_UDeferred : univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____5995 -> false
  
let __proj__UDeferred__item___0 : univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let uu___is_USolved : univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____6009 -> false
  
let __proj__USolved__item___0 : univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let uu___is_UFailed : univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____6023 -> false
  
let __proj__UFailed__item___0 : univ_eq_sol -> Prims.string =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let rec really_solve_universe_eq :
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
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1  in
          let u21 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2  in
          let rec occurs_univ v1 u =
            match u with
            | FStar_Syntax_Syntax.U_max us ->
                FStar_All.pipe_right us
                  (FStar_Util.for_some
                     (fun u3  ->
                        let uu____6061 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____6061 with
                        | (k,uu____6065) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____6069 -> false)))
            | uu____6070 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
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
                        let uu____6117 =
                          really_solve_universe_eq pid_orig wl1 u13 u23  in
                        (match uu____6117 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____6120 -> USolved wl1  in
                  aux wl us1 us2
                else
                  (let uu____6126 =
                     let uu____6127 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____6128 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____6127
                       uu____6128
                      in
                   UFailed uu____6126)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____6144 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____6144 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____6162 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____6162 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____6165 ->
                let uu____6168 =
                  let uu____6169 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____6170 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____6169
                    uu____6170 msg
                   in
                UFailed uu____6168
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____6171,uu____6172) ->
              let uu____6173 =
                let uu____6174 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____6175 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6174 uu____6175
                 in
              failwith uu____6173
          | (FStar_Syntax_Syntax.U_unknown ,uu____6176) ->
              let uu____6177 =
                let uu____6178 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____6179 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6178 uu____6179
                 in
              failwith uu____6177
          | (uu____6180,FStar_Syntax_Syntax.U_bvar uu____6181) ->
              let uu____6182 =
                let uu____6183 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____6184 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6183 uu____6184
                 in
              failwith uu____6182
          | (uu____6185,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____6186 =
                let uu____6187 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____6188 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6187 uu____6188
                 in
              failwith uu____6186
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____6200 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____6200
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____6210 = occurs_univ v1 u3  in
              if uu____6210
              then
                let uu____6211 =
                  let uu____6212 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____6213 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6212 uu____6213
                   in
                try_umax_components u11 u21 uu____6211
              else
                (let uu____6215 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____6215)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____6223 = occurs_univ v1 u3  in
              if uu____6223
              then
                let uu____6224 =
                  let uu____6225 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____6226 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6225 uu____6226
                   in
                try_umax_components u11 u21 uu____6224
              else
                (let uu____6228 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____6228)
          | (FStar_Syntax_Syntax.U_max uu____6231,uu____6232) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____6237 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____6237
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____6239,FStar_Syntax_Syntax.U_max uu____6240) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____6245 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____6245
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____6247,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____6248,FStar_Syntax_Syntax.U_name
             uu____6249) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____6250) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____6251) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6252,FStar_Syntax_Syntax.U_succ
             uu____6253) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6254,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
  
let solve_universe_eq :
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
  
let match_num_binders bc1 bc2 =
  let uu____6324 = bc1  in
  match uu____6324 with
  | (bs1,mk_cod1) ->
      let uu____6349 = bc2  in
      (match uu____6349 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6396 = FStar_Util.first_N n1 bs  in
             match uu____6396 with
             | (bs3,rest) ->
                 let uu____6410 = mk_cod rest  in (bs3, uu____6410)
              in
           let l1 = FStar_List.length bs1  in
           let l2 = FStar_List.length bs2  in
           if l1 = l2
           then
             let uu____6434 =
               let uu____6438 = mk_cod1 []  in (bs1, uu____6438)  in
             let uu____6440 =
               let uu____6444 = mk_cod2 []  in (bs2, uu____6444)  in
             (uu____6434, uu____6440)
           else
             if l1 > l2
             then
               (let uu____6471 = curry l2 bs1 mk_cod1  in
                let uu____6481 =
                  let uu____6485 = mk_cod2 []  in (bs2, uu____6485)  in
                (uu____6471, uu____6481))
             else
               (let uu____6494 =
                  let uu____6498 = mk_cod1 []  in (bs1, uu____6498)  in
                let uu____6500 = curry l1 bs2 mk_cod2  in
                (uu____6494, uu____6500)))
  
let rec solve : FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6607 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____6607
       then
         let uu____6608 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6608
       else ());
      (let uu____6610 = next_prob probs  in
       match uu____6610 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___154_6623 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___154_6623.wl_deferred);
               ctr = (uu___154_6623.ctr);
               defer_ok = (uu___154_6623.defer_ok);
               smt_ok = (uu___154_6623.smt_ok);
               tcenv = (uu___154_6623.tcenv)
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
                  let uu____6630 = solve_flex_rigid_join env tp probs1  in
                  (match uu____6630 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6634 = solve_rigid_flex_meet env tp probs1  in
                     match uu____6634 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____6638,uu____6639) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6648 ->
                let uu____6653 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6681  ->
                          match uu____6681 with
                          | (c,uu____6686,uu____6687) -> c < probs.ctr))
                   in
                (match uu____6653 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6709 =
                            FStar_List.map
                              (fun uu____6715  ->
                                 match uu____6715 with
                                 | (uu____6721,x,y) -> (x, y))
                              probs.wl_deferred
                             in
                          Success uu____6709
                      | uu____6724 ->
                          let uu____6729 =
                            let uu___155_6730 = probs  in
                            let uu____6731 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6740  ->
                                      match uu____6740 with
                                      | (uu____6744,uu____6745,y) -> y))
                               in
                            {
                              attempting = uu____6731;
                              wl_deferred = rest;
                              ctr = (uu___155_6730.ctr);
                              defer_ok = (uu___155_6730.defer_ok);
                              smt_ok = (uu___155_6730.smt_ok);
                              tcenv = (uu___155_6730.tcenv)
                            }  in
                          solve env uu____6729))))

and solve_one_universe_eq :
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
            let uu____6752 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____6752 with
            | USolved wl1 ->
                let uu____6754 = solve_prob orig None [] wl1  in
                solve env uu____6754
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 -> solve env (defer "" orig wl1)

and solve_maybe_uinsts :
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
                  let uu____6788 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____6788 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6791 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6799;
                  FStar_Syntax_Syntax.pos = uu____6800;
                  FStar_Syntax_Syntax.vars = uu____6801;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6804;
                  FStar_Syntax_Syntax.pos = uu____6805;
                  FStar_Syntax_Syntax.vars = uu____6806;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6818,uu____6819) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6824,FStar_Syntax_Syntax.Tm_uinst uu____6825) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6830 -> USolved wl

and giveup_or_defer :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> Prims.string -> solution
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun msg  ->
          if wl.defer_ok
          then
            ((let uu____6838 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____6838
              then
                let uu____6839 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6839 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

and solve_rigid_flex_meet :
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6847 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____6847
         then
           let uu____6848 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6848
         else ());
        (let uu____6850 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____6850 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6892 = head_matches_delta env () t1 t2  in
               match uu____6892 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6914 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____6940 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____6949 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____6950 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____6949, uu____6950)
                          | None  ->
                              let uu____6953 = FStar_Syntax_Subst.compress t1
                                 in
                              let uu____6954 = FStar_Syntax_Subst.compress t2
                                 in
                              (uu____6953, uu____6954)
                           in
                        (match uu____6940 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6976 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____6976
                                in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6999 =
                                    let uu____7005 =
                                      let uu____7008 =
                                        let uu____7011 =
                                          let uu____7012 =
                                            let uu____7017 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2
                                               in
                                            (x, uu____7017)  in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____7012
                                           in
                                        FStar_Syntax_Syntax.mk uu____7011  in
                                      uu____7008 None
                                        t11.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____7030 =
                                      let uu____7032 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort
                                         in
                                      [uu____7032]  in
                                    (uu____7005, uu____7030)  in
                                  Some uu____6999
                              | (uu____7041,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____7043)) ->
                                  let uu____7048 =
                                    let uu____7052 =
                                      let uu____7054 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11
                                         in
                                      [uu____7054]  in
                                    (t11, uu____7052)  in
                                  Some uu____7048
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____7060),uu____7061) ->
                                  let uu____7066 =
                                    let uu____7070 =
                                      let uu____7072 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21
                                         in
                                      [uu____7072]  in
                                    (t21, uu____7070)  in
                                  Some uu____7066
                              | uu____7077 ->
                                  let uu____7080 =
                                    FStar_Syntax_Util.head_and_args t11  in
                                  (match uu____7080 with
                                   | (head1,uu____7095) ->
                                       let uu____7110 =
                                         let uu____7111 =
                                           FStar_Syntax_Util.un_uinst head1
                                            in
                                         uu____7111.FStar_Syntax_Syntax.n  in
                                       (match uu____7110 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____7118;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____7120;_}
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
                                                [FStar_TypeChecker_Normalize.WHNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t11
                                               in
                                            let t22 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Normalize.WHNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t21
                                               in
                                            disjoin t12 t22
                                        | uu____7129 -> None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7138) ->
                  let uu____7151 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___129_7160  ->
                            match uu___129_7160 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____7165 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____7165 with
                                      | (u',uu____7176) ->
                                          let uu____7191 =
                                            let uu____7192 = whnf env u'  in
                                            uu____7192.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____7191 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____7196) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____7209 -> false))
                                 | uu____7210 -> false)
                            | uu____7212 -> false))
                     in
                  (match uu____7151 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____7233 tps =
                         match uu____7233 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____7260 =
                                    let uu____7265 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound uu____7265  in
                                  (match uu____7260 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____7284 -> None)
                          in
                       let uu____7289 =
                         let uu____7294 =
                           let uu____7298 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (uu____7298, [])  in
                         make_lower_bound uu____7294 lower_bounds  in
                       (match uu____7289 with
                        | None  ->
                            ((let uu____7305 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____7305
                              then
                                FStar_Util.print_string "No lower bounds\n"
                              else ());
                             None)
                        | Some (lhs_bound,sub_probs) ->
                            let eq_prob =
                              new_problem env lhs_bound
                                FStar_TypeChecker_Common.EQ
                                tp.FStar_TypeChecker_Common.rhs None
                                tp.FStar_TypeChecker_Common.loc
                                "meeting refinements"
                               in
                            ((let uu____7318 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____7318
                              then
                                let wl' =
                                  let uu___156_7320 = wl  in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___156_7320.wl_deferred);
                                    ctr = (uu___156_7320.ctr);
                                    defer_ok = (uu___156_7320.defer_ok);
                                    smt_ok = (uu___156_7320.smt_ok);
                                    tcenv = (uu___156_7320.tcenv)
                                  }  in
                                let uu____7321 = wl_to_string wl'  in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____7321
                              else ());
                             (let uu____7323 =
                                solve_t env eq_prob
                                  (let uu___157_7324 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___157_7324.wl_deferred);
                                     ctr = (uu___157_7324.ctr);
                                     defer_ok = (uu___157_7324.defer_ok);
                                     smt_ok = (uu___157_7324.smt_ok);
                                     tcenv = (uu___157_7324.tcenv)
                                   })
                                 in
                              match uu____7323 with
                              | Success uu____7326 ->
                                  let wl1 =
                                    let uu___158_7328 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___158_7328.wl_deferred);
                                      ctr = (uu___158_7328.ctr);
                                      defer_ok = (uu___158_7328.defer_ok);
                                      smt_ok = (uu___158_7328.smt_ok);
                                      tcenv = (uu___158_7328.tcenv)
                                    }  in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1
                                     in
                                  let uu____7330 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds
                                     in
                                  Some wl2
                              | uu____7333 -> None))))
              | uu____7334 -> failwith "Impossible: Not a rigid-flex"))

and solve_flex_rigid_join :
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____7341 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____7341
         then
           let uu____7342 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7342
         else ());
        (let uu____7344 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____7344 with
         | (u,args) ->
             let uu____7371 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____7371 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i  in
                  let base_types_match t1 t2 =
                    let uu____7402 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____7402 with
                    | (h1,args1) ->
                        let uu____7430 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____7430 with
                         | (h2,uu____7443) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7462 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  if uu____7462
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____7477 =
                                          let uu____7479 =
                                            let uu____7480 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____7480
                                             in
                                          [uu____7479]  in
                                        Some uu____7477))
                                  else None
                              | (FStar_Syntax_Syntax.Tm_name
                                 a,FStar_Syntax_Syntax.Tm_name b) ->
                                  if FStar_Syntax_Syntax.bv_eq a b
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____7504 =
                                          let uu____7506 =
                                            let uu____7507 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____7507
                                             in
                                          [uu____7506]  in
                                        Some uu____7504))
                                  else None
                              | uu____7515 -> None))
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
                         | None  -> None
                         | Some m1 ->
                             let x1 = FStar_Syntax_Syntax.freshen_bv x  in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x1)]
                                in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1
                                in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2
                                in
                             let uu____7581 =
                               let uu____7587 =
                                 let uu____7590 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21  in
                                 FStar_Syntax_Util.refine x1 uu____7590  in
                               (uu____7587, m1)  in
                             Some uu____7581)
                    | (uu____7599,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7601)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7633),uu____7634) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____7665 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7699) ->
                       let uu____7712 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___130_7721  ->
                                 match uu___130_7721 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____7726 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____7726 with
                                           | (u',uu____7737) ->
                                               let uu____7752 =
                                                 let uu____7753 = whnf env u'
                                                    in
                                                 uu____7753.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____7752 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7757) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____7770 -> false))
                                      | uu____7771 -> false)
                                 | uu____7773 -> false))
                          in
                       (match uu____7712 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7798 tps =
                              match uu____7798 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7839 =
                                         let uu____7846 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound uu____7846  in
                                       (match uu____7839 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7881 -> None)
                               in
                            let uu____7888 =
                              let uu____7895 =
                                let uu____7901 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (uu____7901, [])  in
                              make_upper_bound uu____7895 upper_bounds  in
                            (match uu____7888 with
                             | None  ->
                                 ((let uu____7910 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____7910
                                   then
                                     FStar_Util.print_string
                                       "No upper bounds\n"
                                   else ());
                                  None)
                             | Some (rhs_bound,sub_probs) ->
                                 let eq_prob =
                                   new_problem env
                                     tp.FStar_TypeChecker_Common.lhs
                                     FStar_TypeChecker_Common.EQ rhs_bound
                                     None tp.FStar_TypeChecker_Common.loc
                                     "joining refinements"
                                    in
                                 ((let uu____7929 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____7929
                                   then
                                     let wl' =
                                       let uu___159_7931 = wl  in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___159_7931.wl_deferred);
                                         ctr = (uu___159_7931.ctr);
                                         defer_ok = (uu___159_7931.defer_ok);
                                         smt_ok = (uu___159_7931.smt_ok);
                                         tcenv = (uu___159_7931.tcenv)
                                       }  in
                                     let uu____7932 = wl_to_string wl'  in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7932
                                   else ());
                                  (let uu____7934 =
                                     solve_t env eq_prob
                                       (let uu___160_7935 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___160_7935.wl_deferred);
                                          ctr = (uu___160_7935.ctr);
                                          defer_ok = (uu___160_7935.defer_ok);
                                          smt_ok = (uu___160_7935.smt_ok);
                                          tcenv = (uu___160_7935.tcenv)
                                        })
                                      in
                                   match uu____7934 with
                                   | Success uu____7937 ->
                                       let wl1 =
                                         let uu___161_7939 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___161_7939.wl_deferred);
                                           ctr = (uu___161_7939.ctr);
                                           defer_ok =
                                             (uu___161_7939.defer_ok);
                                           smt_ok = (uu___161_7939.smt_ok);
                                           tcenv = (uu___161_7939.tcenv)
                                         }  in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1
                                          in
                                       let uu____7941 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds
                                          in
                                       Some wl2
                                   | uu____7944 -> None))))
                   | uu____7945 -> failwith "Impossible: Not a flex-rigid")))

and solve_binders :
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
                    let rhs_prob = rhs (FStar_List.rev scope) env1 subst1  in
                    ((let uu____8010 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____8010
                      then
                        let uu____8011 = prob_to_string env1 rhs_prob  in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____8011
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives.fst
                         in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___162_8043 = hd1  in
                      let uu____8044 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___162_8043.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___162_8043.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____8044
                      }  in
                    let hd21 =
                      let uu___163_8048 = hd2  in
                      let uu____8049 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___163_8048.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___163_8048.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____8049
                      }  in
                    let prob =
                      let uu____8053 =
                        let uu____8056 =
                          FStar_All.pipe_left invert_rel (p_rel orig)  in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____8056 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter"
                         in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____8053
                       in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                    let subst2 =
                      let uu____8064 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1
                         in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____8064
                       in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                    let uu____8067 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1  in
                    (match uu____8067 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____8085 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives.fst
                              in
                           let uu____8088 =
                             close_forall env2 [(hd12, imp)] phi  in
                           FStar_Syntax_Util.mk_conj uu____8085 uu____8088
                            in
                         ((let uu____8094 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____8094
                           then
                             let uu____8095 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____8096 =
                               FStar_Syntax_Print.bv_to_string hd12  in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____8095 uu____8096
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____8111 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch"
                 in
              let scope = p_scope orig  in
              let uu____8117 = aux scope env [] bs1 bs2  in
              match uu____8117 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl  in
                  solve env (attempt sub_probs wl1)

and solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____8133 = compress_tprob wl problem  in
        solve_t' env uu____8133 wl

and solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____8166 = head_matches_delta env1 wl1 t1 t2  in
          match uu____8166 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____8183,uu____8184) ->
                   let may_relate head3 =
                     let uu____8199 =
                       let uu____8200 = FStar_Syntax_Util.un_uinst head3  in
                       uu____8200.FStar_Syntax_Syntax.n  in
                     match uu____8199 with
                     | FStar_Syntax_Syntax.Tm_name uu____8203 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____8204 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____8221 -> false  in
                   let uu____8222 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok
                      in
                   if uu____8222
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
                            | Some t ->
                                FStar_Syntax_Util.mk_has_type t11 t t21
                            | None  ->
                                let x = FStar_Syntax_Syntax.new_bv None t11
                                   in
                                let u_x =
                                  env1.FStar_TypeChecker_Env.universe_of env1
                                    t11
                                   in
                                let uu____8239 =
                                  let uu____8240 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____8240 t21
                                   in
                                FStar_Syntax_Util.mk_forall u_x x uu____8239
                             in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1)
                        in
                     let uu____8242 = solve_prob orig (Some guard) [] wl1  in
                     solve env1 uu____8242
                   else
                     (let uu____8244 =
                        let uu____8245 =
                          FStar_Syntax_Print.term_to_string head1  in
                        let uu____8246 =
                          FStar_Syntax_Print.term_to_string head2  in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____8245 uu____8246
                         in
                      giveup env1 uu____8244 orig)
               | (uu____8247,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___164_8255 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___164_8255.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___164_8255.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___164_8255.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___164_8255.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___164_8255.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___164_8255.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___164_8255.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___164_8255.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____8256,None ) ->
                   ((let uu____8263 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____8263
                     then
                       let uu____8264 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____8265 = FStar_Syntax_Print.tag_of_term t1  in
                       let uu____8266 = FStar_Syntax_Print.term_to_string t2
                          in
                       let uu____8267 = FStar_Syntax_Print.tag_of_term t2  in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____8264
                         uu____8265 uu____8266 uu____8267
                     else ());
                    (let uu____8269 = FStar_Syntax_Util.head_and_args t1  in
                     match uu____8269 with
                     | (head11,args1) ->
                         let uu____8295 = FStar_Syntax_Util.head_and_args t2
                            in
                         (match uu____8295 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1  in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____8340 =
                                  let uu____8341 =
                                    FStar_Syntax_Print.term_to_string head11
                                     in
                                  let uu____8342 = args_to_string args1  in
                                  let uu____8343 =
                                    FStar_Syntax_Print.term_to_string head21
                                     in
                                  let uu____8344 = args_to_string args2  in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____8341 uu____8342 uu____8343
                                    uu____8344
                                   in
                                giveup env1 uu____8340 orig
                              else
                                (let uu____8346 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____8351 =
                                        FStar_Syntax_Util.eq_args args1 args2
                                         in
                                      uu____8351 = FStar_Syntax_Util.Equal)
                                    in
                                 if uu____8346
                                 then
                                   let uu____8352 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1
                                      in
                                   match uu____8352 with
                                   | USolved wl2 ->
                                       let uu____8354 =
                                         solve_prob orig None [] wl2  in
                                       solve env1 uu____8354
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____8358 =
                                      base_and_refinement env1 wl1 t1  in
                                    match uu____8358 with
                                    | (base1,refinement1) ->
                                        let uu____8384 =
                                          base_and_refinement env1 wl1 t2  in
                                        (match uu____8384 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____8438 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1
                                                     in
                                                  (match uu____8438 with
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
                                                           (fun uu____8448 
                                                              ->
                                                              fun uu____8449 
                                                                ->
                                                                match 
                                                                  (uu____8448,
                                                                    uu____8449)
                                                                with
                                                                | ((a,uu____8459),
                                                                   (a',uu____8461))
                                                                    ->
                                                                    let uu____8466
                                                                    =
                                                                    mk_problem
                                                                    (p_scope
                                                                    orig)
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a' None
                                                                    "index"
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    (fun
                                                                    _0_56  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_56)
                                                                    uu____8466)
                                                           args1 args2
                                                          in
                                                       let formula =
                                                         let uu____8472 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                fst
                                                                  (p_guard p))
                                                             subprobs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8472
                                                          in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2
                                                          in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8476 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1)
                                                     in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2)
                                                     in
                                                  solve_t env1
                                                    (let uu___165_8509 =
                                                       problem  in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___165_8509.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___165_8509.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___165_8509.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___165_8509.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___165_8509.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___165_8509.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___165_8509.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___165_8509.FStar_TypeChecker_Common.rank)
                                                     }) wl1))))))))
           in
        let imitate orig env1 wl1 p =
          let uu____8529 = p  in
          match uu____8529 with
          | (((u,k),xs,c),ps,(h,uu____8540,qs)) ->
              let xs1 = sn_binders env1 xs  in
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____8589 = imitation_sub_probs orig env1 xs1 ps qs  in
              (match uu____8589 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8603 = h gs_xs  in
                     let uu____8604 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> Some _0_57)
                        in
                     FStar_Syntax_Util.abs xs1 uu____8603 uu____8604  in
                   ((let uu____8608 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____8608
                     then
                       let uu____8609 =
                         FStar_Syntax_Print.binders_to_string ", " xs1  in
                       let uu____8610 = FStar_Syntax_Print.comp_to_string c
                          in
                       let uu____8611 = FStar_Syntax_Print.term_to_string im
                          in
                       let uu____8612 = FStar_Syntax_Print.tag_of_term im  in
                       let uu____8613 =
                         let uu____8614 =
                           FStar_List.map (prob_to_string env1) sub_probs  in
                         FStar_All.pipe_right uu____8614
                           (FStar_String.concat ", ")
                          in
                       let uu____8617 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula
                          in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8609 uu____8610 uu____8611 uu____8612
                         uu____8613 uu____8617
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1
                        in
                     solve env1 (attempt sub_probs wl2))))
           in
        let imitate' orig env1 wl1 uu___131_8635 =
          match uu___131_8635 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p  in
        let project orig env1 wl1 i p =
          let uu____8664 = p  in
          match uu____8664 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____8722 = FStar_List.nth ps i  in
              (match uu____8722 with
               | (pi,uu____8725) ->
                   let uu____8730 = FStar_List.nth xs i  in
                   (match uu____8730 with
                    | (xi,uu____8737) ->
                        let rec gs k =
                          let uu____8746 = FStar_Syntax_Util.arrow_formals k
                             in
                          match uu____8746 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8798)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort
                                       in
                                    let uu____8806 = new_uvar r xs k_a  in
                                    (match uu____8806 with
                                     | (gi_xs,gi) ->
                                         let gi_xs1 =
                                           FStar_TypeChecker_Normalize.eta_expand
                                             env1 gi_xs
                                            in
                                         let gi_ps =
                                           (FStar_Syntax_Syntax.mk_Tm_app gi
                                              ps)
                                             (Some
                                                (k_a.FStar_Syntax_Syntax.n))
                                             r
                                            in
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT
                                              (a, gi_xs1))
                                           :: subst1  in
                                         let uu____8825 = aux subst2 tl1  in
                                         (match uu____8825 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8840 =
                                                let uu____8842 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1
                                                   in
                                                uu____8842 :: gi_xs'  in
                                              let uu____8843 =
                                                let uu____8845 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps
                                                   in
                                                uu____8845 :: gi_ps'  in
                                              (uu____8840, uu____8843)))
                                 in
                              aux [] bs
                           in
                        let uu____8848 =
                          let uu____8849 = matches pi  in
                          FStar_All.pipe_left Prims.op_Negation uu____8849
                           in
                        if uu____8848
                        then None
                        else
                          (let uu____8852 = gs xi.FStar_Syntax_Syntax.sort
                              in
                           match uu____8852 with
                           | (g_xs,uu____8859) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                  in
                               let proj =
                                 let uu____8866 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r
                                    in
                                 let uu____8871 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c) (fun _0_58  -> Some _0_58)
                                    in
                                 FStar_Syntax_Util.abs xs uu____8866
                                   uu____8871
                                  in
                               let sub1 =
                                 let uu____8875 =
                                   let uu____8878 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r
                                      in
                                   let uu____8885 =
                                     let uu____8888 =
                                       FStar_List.map
                                         (fun uu____8894  ->
                                            match uu____8894 with
                                            | (uu____8899,uu____8900,y) -> y)
                                         qs
                                        in
                                     FStar_All.pipe_left h uu____8888  in
                                   mk_problem (p_scope orig) orig uu____8878
                                     (p_rel orig) uu____8885 None
                                     "projection"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____8875
                                  in
                               ((let uu____8910 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____8910
                                 then
                                   let uu____8911 =
                                     FStar_Syntax_Print.term_to_string proj
                                      in
                                   let uu____8912 = prob_to_string env1 sub1
                                      in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8911 uu____8912
                                 else ());
                                (let wl2 =
                                   let uu____8915 =
                                     let uu____8917 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives.fst (p_guard sub1)
                                        in
                                     Some uu____8917  in
                                   solve_prob orig uu____8915
                                     [TERM (u, proj)] wl1
                                    in
                                 let uu____8922 =
                                   solve env1 (attempt [sub1] wl2)  in
                                 FStar_All.pipe_left
                                   (fun _0_60  -> Some _0_60) uu____8922)))))
           in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8946 = lhs  in
          match uu____8946 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8969 = FStar_Syntax_Util.arrow_formals_comp k_uv
                   in
                match uu____8969 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8995 =
                        let uu____9021 = decompose env t2  in
                        (((uv, k_uv), xs, c), ps, uu____9021)  in
                      Some uu____8995
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv
                          in
                       let rec elim k args =
                         let uu____9104 =
                           let uu____9108 =
                             let uu____9109 = FStar_Syntax_Subst.compress k
                                in
                             uu____9109.FStar_Syntax_Syntax.n  in
                           (uu____9108, args)  in
                         match uu____9104 with
                         | (uu____9116,[]) ->
                             let uu____9118 =
                               let uu____9124 =
                                 FStar_Syntax_Syntax.mk_Total k  in
                               ([], uu____9124)  in
                             Some uu____9118
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____9135,uu____9136) ->
                             let uu____9147 =
                               FStar_Syntax_Util.head_and_args k  in
                             (match uu____9147 with
                              | (uv1,uv_args) ->
                                  let uu____9176 =
                                    let uu____9177 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____9177.FStar_Syntax_Syntax.n  in
                                  (match uu____9176 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9184) ->
                                       let uu____9197 =
                                         pat_vars env [] uv_args  in
                                       (match uu____9197 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9211  ->
                                                      let uu____9212 =
                                                        let uu____9213 =
                                                          let uu____9214 =
                                                            let uu____9217 =
                                                              let uu____9218
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____9218
                                                                FStar_Pervasives.fst
                                                               in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9217
                                                             in
                                                          fst uu____9214  in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9213
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9212))
                                               in
                                            let c1 =
                                              let uu____9224 =
                                                let uu____9225 =
                                                  let uu____9228 =
                                                    let uu____9229 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____9229
                                                      FStar_Pervasives.fst
                                                     in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9228
                                                   in
                                                fst uu____9225  in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9224
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____9238 =
                                                let uu____9240 =
                                                  let uu____9241 =
                                                    let uu____9244 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____9244
                                                      FStar_Pervasives.fst
                                                     in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____9241
                                                   in
                                                Some uu____9240  in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9238
                                               in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9254 -> None))
                         | (FStar_Syntax_Syntax.Tm_app uu____9257,uu____9258)
                             ->
                             let uu____9270 =
                               FStar_Syntax_Util.head_and_args k  in
                             (match uu____9270 with
                              | (uv1,uv_args) ->
                                  let uu____9299 =
                                    let uu____9300 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____9300.FStar_Syntax_Syntax.n  in
                                  (match uu____9299 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9307) ->
                                       let uu____9320 =
                                         pat_vars env [] uv_args  in
                                       (match uu____9320 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9334  ->
                                                      let uu____9335 =
                                                        let uu____9336 =
                                                          let uu____9337 =
                                                            let uu____9340 =
                                                              let uu____9341
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____9341
                                                                FStar_Pervasives.fst
                                                               in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9340
                                                             in
                                                          fst uu____9337  in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9336
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9335))
                                               in
                                            let c1 =
                                              let uu____9347 =
                                                let uu____9348 =
                                                  let uu____9351 =
                                                    let uu____9352 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____9352
                                                      FStar_Pervasives.fst
                                                     in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9351
                                                   in
                                                fst uu____9348  in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9347
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____9361 =
                                                let uu____9363 =
                                                  let uu____9364 =
                                                    let uu____9367 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____9367
                                                      FStar_Pervasives.fst
                                                     in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____9364
                                                   in
                                                Some uu____9363  in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9361
                                               in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____9377 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____9382)
                             ->
                             let n_args = FStar_List.length args  in
                             let n_xs = FStar_List.length xs1  in
                             if n_xs = n_args
                             then
                               let uu____9414 =
                                 FStar_Syntax_Subst.open_comp xs1 c1  in
                               FStar_All.pipe_right uu____9414
                                 (fun _0_61  -> Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9438 =
                                    FStar_Util.first_N n_xs args  in
                                  match uu____9438 with
                                  | (args1,rest) ->
                                      let uu____9456 =
                                        FStar_Syntax_Subst.open_comp xs1 c1
                                         in
                                      (match uu____9456 with
                                       | (xs2,c2) ->
                                           let uu____9464 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest
                                              in
                                           FStar_Util.bind_opt uu____9464
                                             (fun uu____9475  ->
                                                match uu____9475 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9497 =
                                    FStar_Util.first_N n_args xs1  in
                                  match uu____9497 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____9545 =
                                        let uu____9548 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9548
                                         in
                                      FStar_All.pipe_right uu____9545
                                        (fun _0_62  -> Some _0_62))
                         | uu____9556 ->
                             let uu____9560 =
                               let uu____9561 =
                                 FStar_Syntax_Print.uvar_to_string uv  in
                               let uu____9562 =
                                 FStar_Syntax_Print.term_to_string k  in
                               let uu____9563 =
                                 FStar_Syntax_Print.term_to_string k_uv1  in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9561 uu____9562 uu____9563
                                in
                             failwith uu____9560
                          in
                       let uu____9567 = elim k_uv1 ps  in
                       FStar_Util.bind_opt uu____9567
                         (fun uu____9595  ->
                            match uu____9595 with
                            | (xs1,c1) ->
                                let uu____9623 =
                                  let uu____9646 = decompose env t2  in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9646)
                                   in
                                Some uu____9623))
                 in
              let rec imitate_or_project n1 stopt i =
                if (i >= n1) || (FStar_Option.isNone stopt)
                then
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig
                else
                  (let st = FStar_Option.get stopt  in
                   let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                   if i = (~- (Prims.parse_int "1"))
                   then
                     let uu____9718 = imitate orig env wl1 st  in
                     match uu____9718 with
                     | Failed uu____9723 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9729 = project orig env wl1 i st  in
                      match uu____9729 with
                      | None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some (Failed uu____9736) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol))
                 in
              let check_head fvs1 t21 =
                let uu____9750 = FStar_Syntax_Util.head_and_args t21  in
                match uu____9750 with
                | (hd1,uu____9761) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9776 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9784 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____9785 -> true
                     | uu____9795 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1  in
                         let uu____9798 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1  in
                         if uu____9798
                         then true
                         else
                           ((let uu____9801 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____9801
                             then
                               let uu____9802 = names_to_string fvs_hd  in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____9802
                             else ());
                            false))
                 in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____9810 =
                    let uu____9813 = FStar_Syntax_Util.head_and_args t21  in
                    FStar_All.pipe_right uu____9813 FStar_Pervasives.fst  in
                  FStar_All.pipe_right uu____9810 FStar_Syntax_Free.names  in
                let uu____9844 = FStar_Util.set_is_empty fvs_hd  in
                if uu____9844
                then ~- (Prims.parse_int "1")
                else (Prims.parse_int "0")  in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1  in
                   let t21 = sn env t2  in
                   let fvs1 = FStar_Syntax_Free.names t11  in
                   let fvs2 = FStar_Syntax_Free.names t21  in
                   let uu____9853 = occurs_check env wl1 (uv, k_uv) t21  in
                   (match uu____9853 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____9861 =
                            let uu____9862 = FStar_Option.get msg  in
                            Prims.strcat "occurs-check failed: " uu____9862
                             in
                          giveup_or_defer1 orig uu____9861
                        else
                          (let uu____9864 =
                             FStar_Util.set_is_subset_of fvs2 fvs1  in
                           if uu____9864
                           then
                             let uu____9865 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
                                in
                             (if uu____9865
                              then
                                let uu____9866 = subterms args_lhs  in
                                imitate' orig env wl1 uu____9866
                              else
                                ((let uu____9870 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____9870
                                  then
                                    let uu____9871 =
                                      FStar_Syntax_Print.term_to_string t11
                                       in
                                    let uu____9872 = names_to_string fvs1  in
                                    let uu____9873 = names_to_string fvs2  in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9871 uu____9872 uu____9873
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9878 ->
                                        let uu____9879 = sn_binders env vars
                                           in
                                        u_abs k_uv uu____9879 t21
                                     in
                                  let wl2 =
                                    solve_prob orig None
                                      [TERM ((uv, k_uv), sol)] wl1
                                     in
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
                               (let uu____9888 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21)
                                   in
                                if uu____9888
                                then
                                  ((let uu____9890 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____9890
                                    then
                                      let uu____9891 =
                                        FStar_Syntax_Print.term_to_string t11
                                         in
                                      let uu____9892 = names_to_string fvs1
                                         in
                                      let uu____9893 = names_to_string fvs2
                                         in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9891 uu____9892 uu____9893
                                    else ());
                                   (let uu____9895 = subterms args_lhs  in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9895
                                      (~- (Prims.parse_int "1"))))
                                else
                                  giveup env
                                    "free-variable check failed on a non-redex"
                                    orig)))
               | None  when patterns_only -> giveup env "not a pattern" orig
               | None  ->
                   if wl1.defer_ok
                   then solve env (defer "not a pattern" orig wl1)
                   else
                     (let uu____9909 =
                        let uu____9910 = FStar_Syntax_Free.names t1  in
                        check_head uu____9910 t2  in
                      if uu____9909
                      then
                        let im_ok = imitate_ok t2  in
                        ((let uu____9914 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel")
                             in
                          if uu____9914
                          then
                            let uu____9915 =
                              FStar_Syntax_Print.term_to_string t1  in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9915
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9918 = subterms args_lhs  in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9918 im_ok))
                      else giveup env "head-symbol is free" orig))
           in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9963 =
               match uu____9963 with
               | (t,u,k,args) ->
                   let k1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta] env k
                      in
                   let uu____9994 = FStar_Syntax_Util.arrow_formals k1  in
                   (match uu____9994 with
                    | (all_formals,uu____10005) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____10097  ->
                                        match uu____10097 with
                                        | (x,imp) ->
                                            let uu____10104 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            (uu____10104, imp)))
                                 in
                              let pattern_vars1 = FStar_List.rev pattern_vars
                                 in
                              let kk =
                                let uu____10112 = FStar_Syntax_Util.type_u ()
                                   in
                                match uu____10112 with
                                | (t1,uu____10116) ->
                                    let uu____10117 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1
                                       in
                                    fst uu____10117
                                 in
                              let uu____10120 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk
                                 in
                              (match uu____10120 with
                               | (t',tm_u1) ->
                                   let uu____10127 = destruct_flex_t t'  in
                                   (match uu____10127 with
                                    | (uu____10147,u1,k11,uu____10150) ->
                                        let sol =
                                          let uu____10178 =
                                            let uu____10183 =
                                              u_abs k1 all_formals t'  in
                                            ((u, k1), uu____10183)  in
                                          TERM uu____10178  in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos
                                           in
                                        (sol, (t_app, u1, k11, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____10243 = pat_var_opt env pat_args hd1
                                 in
                              (match uu____10243 with
                               | None  ->
                                   aux pat_args pattern_vars pattern_var_set
                                     formals1 tl1
                               | Some y ->
                                   let maybe_pat =
                                     match xs_opt with
                                     | None  -> true
                                     | Some xs ->
                                         FStar_All.pipe_right xs
                                           (FStar_Util.for_some
                                              (fun uu____10272  ->
                                                 match uu____10272 with
                                                 | (x,uu____10276) ->
                                                     FStar_Syntax_Syntax.bv_eq
                                                       x (fst y)))
                                      in
                                   if Prims.op_Negation maybe_pat
                                   then
                                     aux pat_args pattern_vars
                                       pattern_var_set formals1 tl1
                                   else
                                     (let fvs =
                                        FStar_Syntax_Free.names
                                          (fst y).FStar_Syntax_Syntax.sort
                                         in
                                      let uu____10282 =
                                        let uu____10283 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set
                                           in
                                        Prims.op_Negation uu____10283  in
                                      if uu____10282
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____10287 =
                                           FStar_Util.set_add (fst formal)
                                             pattern_var_set
                                            in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____10287 formals1
                                           tl1)))
                          | uu____10293 -> failwith "Impossible"  in
                        let uu____10304 = FStar_Syntax_Syntax.new_bv_set ()
                           in
                        aux [] [] uu____10304 all_formals args)
                in
             let solve_both_pats wl1 uu____10344 uu____10345 r =
               match (uu____10344, uu____10345) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10459 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys)
                      in
                   if uu____10459
                   then
                     let uu____10460 = solve_prob orig None [] wl1  in
                     solve env uu____10460
                   else
                     (let xs1 = sn_binders env xs  in
                      let ys1 = sn_binders env ys  in
                      let zs = intersect_vars xs1 ys1  in
                      (let uu____10475 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____10475
                       then
                         let uu____10476 =
                           FStar_Syntax_Print.binders_to_string ", " xs1  in
                         let uu____10477 =
                           FStar_Syntax_Print.binders_to_string ", " ys1  in
                         let uu____10478 =
                           FStar_Syntax_Print.binders_to_string ", " zs  in
                         let uu____10479 =
                           FStar_Syntax_Print.term_to_string k1  in
                         let uu____10480 =
                           FStar_Syntax_Print.term_to_string k2  in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10476 uu____10477 uu____10478 uu____10479
                           uu____10480
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2  in
                         let args_len = FStar_List.length args  in
                         if xs_len = args_len
                         then
                           let uu____10528 =
                             FStar_Syntax_Util.subst_of_list xs2 args  in
                           FStar_Syntax_Subst.subst uu____10528 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10541 =
                                FStar_Util.first_N args_len xs2  in
                              match uu____10541 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10573 =
                                      FStar_Syntax_Syntax.mk_GTotal k  in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10573
                                     in
                                  let uu____10576 =
                                    FStar_Syntax_Util.subst_of_list xs3 args
                                     in
                                  FStar_Syntax_Subst.subst uu____10576 k3)
                           else
                             (let uu____10579 =
                                let uu____10580 =
                                  FStar_Syntax_Print.term_to_string k  in
                                let uu____10581 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2
                                   in
                                let uu____10582 =
                                  FStar_Syntax_Print.args_to_string args  in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10580 uu____10581 uu____10582
                                 in
                              failwith uu____10579)
                          in
                       let uu____10583 =
                         let uu____10589 =
                           let uu____10597 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1
                              in
                           FStar_Syntax_Util.arrow_formals uu____10597  in
                         match uu____10589 with
                         | (bs,k1') ->
                             let uu____10615 =
                               let uu____10623 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2
                                  in
                               FStar_Syntax_Util.arrow_formals uu____10623
                                in
                             (match uu____10615 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1  in
                                  let k2'_ys = subst_k k2' cs args2  in
                                  let sub_prob =
                                    let uu____10644 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____10644
                                     in
                                  let uu____10649 =
                                    let uu____10652 =
                                      let uu____10653 =
                                        FStar_Syntax_Subst.compress k1'  in
                                      uu____10653.FStar_Syntax_Syntax.n  in
                                    let uu____10656 =
                                      let uu____10657 =
                                        FStar_Syntax_Subst.compress k2'  in
                                      uu____10657.FStar_Syntax_Syntax.n  in
                                    (uu____10652, uu____10656)  in
                                  (match uu____10649 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10665,uu____10666) ->
                                       (k1', [sub_prob])
                                   | (uu____10670,FStar_Syntax_Syntax.Tm_type
                                      uu____10671) -> (k2', [sub_prob])
                                   | uu____10675 ->
                                       let uu____10678 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____10678 with
                                        | (t,uu____10687) ->
                                            let uu____10688 = new_uvar r zs t
                                               in
                                            (match uu____10688 with
                                             | (k_zs,uu____10697) ->
                                                 let kprob =
                                                   let uu____10699 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding"
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_64  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_64) uu____10699
                                                    in
                                                 (k_zs, [sub_prob; kprob])))))
                          in
                       match uu____10583 with
                       | (k_u',sub_probs) ->
                           let uu____10713 =
                             let uu____10721 =
                               let uu____10722 = new_uvar r zs k_u'  in
                               FStar_All.pipe_left FStar_Pervasives.fst
                                 uu____10722
                                in
                             let uu____10727 =
                               let uu____10730 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow xs1 uu____10730  in
                             let uu____10733 =
                               let uu____10736 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow ys1 uu____10736  in
                             (uu____10721, uu____10727, uu____10733)  in
                           (match uu____10713 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs  in
                                let uu____10755 =
                                  occurs_check env wl1 (u1, k1) sub1  in
                                (match uu____10755 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1)  in
                                        let uu____10767 =
                                          FStar_Syntax_Unionfind.equiv u1 u2
                                           in
                                        if uu____10767
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1
                                             in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs
                                              in
                                           let uu____10771 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2
                                              in
                                           match uu____10771 with
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
                                                    solve_prob orig None
                                                      [sol1; sol2] wl1
                                                     in
                                                  solve env
                                                    (attempt sub_probs wl2))))))))
                in
             let solve_one_pat uu____10803 uu____10804 =
               match (uu____10803, uu____10804) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10868 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____10868
                     then
                       let uu____10869 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____10870 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10869 uu____10870
                     else ());
                    (let uu____10872 = FStar_Syntax_Unionfind.equiv u1 u2  in
                     if uu____10872
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10879  ->
                              fun uu____10880  ->
                                match (uu____10879, uu____10880) with
                                | ((a,uu____10890),(t21,uu____10892)) ->
                                    let uu____10897 =
                                      let uu____10900 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      mk_problem (p_scope orig) orig
                                        uu____10900
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index"
                                       in
                                    FStar_All.pipe_right uu____10897
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2
                          in
                       let guard =
                         let uu____10904 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives.fst) sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____10904  in
                       let wl1 = solve_prob orig (Some guard) [] wl  in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2  in
                        let rhs_vars = FStar_Syntax_Free.names t21  in
                        let uu____10914 = occurs_check env wl (u1, k1) t21
                           in
                        match uu____10914 with
                        | (occurs_ok,uu____10919) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs  in
                            let uu____10924 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars)
                               in
                            if uu____10924
                            then
                              let sol =
                                let uu____10926 =
                                  let uu____10931 = u_abs k1 xs t21  in
                                  ((u1, k1), uu____10931)  in
                                TERM uu____10926  in
                              let wl1 = solve_prob orig None [sol] wl  in
                              solve env wl1
                            else
                              (let uu____10936 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok)
                                  in
                               if uu____10936
                               then
                                 let uu____10937 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2)
                                    in
                                 match uu____10937 with
                                 | (sol,(uu____10947,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl
                                        in
                                     ((let uu____10957 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern")
                                          in
                                       if uu____10957
                                       then
                                         let uu____10958 =
                                           uvi_to_string env sol  in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10958
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____10963 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint"))))
                in
             let uu____10965 = lhs  in
             match uu____10965 with
             | (t1,u1,k1,args1) ->
                 let uu____10970 = rhs  in
                 (match uu____10970 with
                  | (t2,u2,k2,args2) ->
                      let maybe_pat_vars1 = pat_vars env [] args1  in
                      let maybe_pat_vars2 = pat_vars env [] args2  in
                      let r = t2.FStar_Syntax_Syntax.pos  in
                      (match (maybe_pat_vars1, maybe_pat_vars2) with
                       | (Some xs,Some ys) ->
                           solve_both_pats wl (u1, k1, xs, args1)
                             (u2, k2, ys, args2) t2.FStar_Syntax_Syntax.pos
                       | (Some xs,None ) ->
                           solve_one_pat (t1, u1, k1, xs) rhs
                       | (None ,Some ys) ->
                           solve_one_pat (t2, u2, k2, ys) lhs
                       | uu____10996 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____11002 =
                                force_quasi_pattern None (t1, u1, k1, args1)
                                 in
                              match uu____11002 with
                              | (sol,uu____11009) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl  in
                                  ((let uu____11012 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern")
                                       in
                                    if uu____11012
                                    then
                                      let uu____11013 = uvi_to_string env sol
                                         in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____11013
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____11018 ->
                                        giveup env "impossible" orig))))))
           in
        let orig = FStar_TypeChecker_Common.TProb problem  in
        let uu____11020 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs
           in
        if uu____11020
        then
          let uu____11021 = solve_prob orig None [] wl  in
          solve env uu____11021
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs  in
           let t2 = problem.FStar_TypeChecker_Common.rhs  in
           let uu____11025 = FStar_Util.physical_equality t1 t2  in
           if uu____11025
           then
             let uu____11026 = solve_prob orig None [] wl  in
             solve env uu____11026
           else
             ((let uu____11029 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck")
                  in
               if uu____11029
               then
                 let uu____11030 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid
                    in
                 FStar_Util.print1 "Attempting %s\n" uu____11030
               else ());
              (let r = FStar_TypeChecker_Env.get_range env  in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____11033,uu____11034) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____11035,FStar_Syntax_Syntax.Tm_bvar uu____11036) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___132_11076 =
                     match uu___132_11076 with
                     | [] -> c
                     | bs ->
                         let uu____11090 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c)) None
                             c.FStar_Syntax_Syntax.pos
                            in
                         FStar_Syntax_Syntax.mk_Total uu____11090
                      in
                   let uu____11100 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                   (match uu____11100 with
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
                                   let uu____11186 =
                                     FStar_Options.use_eq_at_higher_order ()
                                      in
                                   if uu____11186
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation
                                    in
                                 let uu____11188 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____11188))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___133_11240 =
                     match uu___133_11240 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l)) None
                           t.FStar_Syntax_Syntax.pos
                      in
                   let uu____11265 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2))
                      in
                   (match uu____11265 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____11348 =
                                   let uu____11351 =
                                     FStar_Syntax_Subst.subst subst1 tbody11
                                      in
                                   let uu____11352 =
                                     FStar_Syntax_Subst.subst subst1 tbody21
                                      in
                                   mk_problem scope orig uu____11351
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____11352 None "lambda co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____11348))
               | (FStar_Syntax_Syntax.Tm_abs uu____11355,uu____11356) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11374 -> true
                     | uu____11384 -> false  in
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
                   let uu____11412 =
                     let uu____11423 = maybe_eta t1  in
                     let uu____11428 = maybe_eta t2  in
                     (uu____11423, uu____11428)  in
                   (match uu____11412 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_11459 = problem  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_11459.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_11459.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_11459.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_11459.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_11459.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_11459.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_11459.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_11459.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11478 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____11478
                        then
                          let uu____11479 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____11479 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11500 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____11500
                        then
                          let uu____11501 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____11501 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11506 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11517,FStar_Syntax_Syntax.Tm_abs uu____11518) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11536 -> true
                     | uu____11546 -> false  in
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
                   let uu____11574 =
                     let uu____11585 = maybe_eta t1  in
                     let uu____11590 = maybe_eta t2  in
                     (uu____11585, uu____11590)  in
                   (match uu____11574 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_11621 = problem  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_11621.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_11621.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_11621.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_11621.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_11621.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_11621.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_11621.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_11621.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11640 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____11640
                        then
                          let uu____11641 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____11641 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11662 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____11662
                        then
                          let uu____11663 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____11663 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11668 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11679,FStar_Syntax_Syntax.Tm_refine uu____11680) ->
                   let uu____11689 = as_refinement env wl t1  in
                   (match uu____11689 with
                    | (x1,phi1) ->
                        let uu____11694 = as_refinement env wl t2  in
                        (match uu____11694 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11700 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____11700
                                in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1  in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)]
                                in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1
                                in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2
                                in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11
                                in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____11733 = imp phi12 phi22  in
                               FStar_All.pipe_right uu____11733
                                 (guard_on_element wl problem x11)
                                in
                             let fallback uu____11737 =
                               let impl =
                                 if
                                   problem.FStar_TypeChecker_Common.relation
                                     = FStar_TypeChecker_Common.EQ
                                 then
                                   mk_imp1 FStar_Syntax_Util.mk_iff phi11
                                     phi21
                                 else
                                   mk_imp1 FStar_Syntax_Util.mk_imp phi11
                                     phi21
                                  in
                               let guard =
                                 let uu____11743 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____11743 impl
                                  in
                               let wl1 = solve_prob orig (Some guard) [] wl
                                  in
                               solve env1 (attempt [base_prob] wl1)  in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____11750 =
                                   let uu____11753 =
                                     let uu____11754 =
                                       FStar_Syntax_Syntax.mk_binder x11  in
                                     uu____11754 :: (p_scope orig)  in
                                   mk_problem uu____11753 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____11750
                                  in
                               let uu____11757 =
                                 solve env1
                                   (let uu___167_11758 = wl  in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___167_11758.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___167_11758.smt_ok);
                                      tcenv = (uu___167_11758.tcenv)
                                    })
                                  in
                               (match uu____11757 with
                                | Failed uu____11762 -> fallback ()
                                | Success uu____11765 ->
                                    let guard =
                                      let uu____11769 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives.fst
                                         in
                                      let uu____11772 =
                                        let uu____11773 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives.fst
                                           in
                                        FStar_All.pipe_right uu____11773
                                          (guard_on_element wl problem x11)
                                         in
                                      FStar_Syntax_Util.mk_conj uu____11769
                                        uu____11772
                                       in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl  in
                                    let wl2 =
                                      let uu___168_11780 = wl1  in
                                      {
                                        attempting =
                                          (uu___168_11780.attempting);
                                        wl_deferred =
                                          (uu___168_11780.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___168_11780.defer_ok);
                                        smt_ok = (uu___168_11780.smt_ok);
                                        tcenv = (uu___168_11780.tcenv)
                                      }  in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11782,FStar_Syntax_Syntax.Tm_uvar uu____11783) ->
                   let uu____11800 = destruct_flex_t t1  in
                   let uu____11801 = destruct_flex_t t2  in
                   flex_flex1 orig uu____11800 uu____11801
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11802;
                     FStar_Syntax_Syntax.tk = uu____11803;
                     FStar_Syntax_Syntax.pos = uu____11804;
                     FStar_Syntax_Syntax.vars = uu____11805;_},uu____11806),FStar_Syntax_Syntax.Tm_uvar
                  uu____11807) ->
                   let uu____11838 = destruct_flex_t t1  in
                   let uu____11839 = destruct_flex_t t2  in
                   flex_flex1 orig uu____11838 uu____11839
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11840,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11841;
                     FStar_Syntax_Syntax.tk = uu____11842;
                     FStar_Syntax_Syntax.pos = uu____11843;
                     FStar_Syntax_Syntax.vars = uu____11844;_},uu____11845))
                   ->
                   let uu____11876 = destruct_flex_t t1  in
                   let uu____11877 = destruct_flex_t t2  in
                   flex_flex1 orig uu____11876 uu____11877
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11878;
                     FStar_Syntax_Syntax.tk = uu____11879;
                     FStar_Syntax_Syntax.pos = uu____11880;
                     FStar_Syntax_Syntax.vars = uu____11881;_},uu____11882),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11883;
                     FStar_Syntax_Syntax.tk = uu____11884;
                     FStar_Syntax_Syntax.pos = uu____11885;
                     FStar_Syntax_Syntax.vars = uu____11886;_},uu____11887))
                   ->
                   let uu____11932 = destruct_flex_t t1  in
                   let uu____11933 = destruct_flex_t t2  in
                   flex_flex1 orig uu____11932 uu____11933
               | (FStar_Syntax_Syntax.Tm_uvar uu____11934,uu____11935) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11944 = destruct_flex_pattern env t1  in
                   solve_t_flex_rigid false orig uu____11944 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11948;
                     FStar_Syntax_Syntax.tk = uu____11949;
                     FStar_Syntax_Syntax.pos = uu____11950;
                     FStar_Syntax_Syntax.vars = uu____11951;_},uu____11952),uu____11953)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11976 = destruct_flex_pattern env t1  in
                   solve_t_flex_rigid false orig uu____11976 t2 wl
               | (uu____11980,FStar_Syntax_Syntax.Tm_uvar uu____11981) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____11990,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11991;
                     FStar_Syntax_Syntax.tk = uu____11992;
                     FStar_Syntax_Syntax.pos = uu____11993;
                     FStar_Syntax_Syntax.vars = uu____11994;_},uu____11995))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12018,FStar_Syntax_Syntax.Tm_type uu____12019) ->
                   solve_t' env
                     (let uu___169_12028 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12028.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12028.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12028.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12028.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12028.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12028.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12028.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12028.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12028.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12029;
                     FStar_Syntax_Syntax.tk = uu____12030;
                     FStar_Syntax_Syntax.pos = uu____12031;
                     FStar_Syntax_Syntax.vars = uu____12032;_},uu____12033),FStar_Syntax_Syntax.Tm_type
                  uu____12034) ->
                   solve_t' env
                     (let uu___169_12057 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12057.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12057.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12057.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12057.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12057.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12057.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12057.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12057.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12057.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12058,FStar_Syntax_Syntax.Tm_arrow uu____12059) ->
                   solve_t' env
                     (let uu___169_12075 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12075.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12075.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12075.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12075.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12075.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12075.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12075.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12075.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12075.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12076;
                     FStar_Syntax_Syntax.tk = uu____12077;
                     FStar_Syntax_Syntax.pos = uu____12078;
                     FStar_Syntax_Syntax.vars = uu____12079;_},uu____12080),FStar_Syntax_Syntax.Tm_arrow
                  uu____12081) ->
                   solve_t' env
                     (let uu___169_12111 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12111.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12111.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12111.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12111.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12111.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12111.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12111.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12111.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12111.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____12112,uu____12113) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation
                         in
                      let uu____12124 =
                        let uu____12125 = is_top_level_prob orig  in
                        FStar_All.pipe_left Prims.op_Negation uu____12125  in
                      if uu____12124
                      then
                        let uu____12126 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___170_12129 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_12129.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_12129.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_12129.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_12129.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_12129.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_12129.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_12129.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_12129.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_12129.FStar_TypeChecker_Common.rank)
                             })
                           in
                        let uu____12130 = destruct_flex_pattern env t1  in
                        solve_t_flex_rigid false uu____12126 uu____12130 t2
                          wl
                      else
                        (let uu____12135 = base_and_refinement env wl t2  in
                         match uu____12135 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12165 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___171_12168 = problem  in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_12168.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_12168.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_12168.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_12168.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_12168.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_12168.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_12168.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_12168.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_12168.FStar_TypeChecker_Common.rank)
                                       })
                                     in
                                  let uu____12169 =
                                    destruct_flex_pattern env t1  in
                                  solve_t_flex_rigid false uu____12165
                                    uu____12169 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___172_12184 = y  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_12184.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_12184.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }  in
                                  let impl =
                                    guard_on_element wl problem y' phi  in
                                  let base_prob =
                                    let uu____12187 =
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
                                      uu____12187
                                     in
                                  let guard =
                                    let uu____12195 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst
                                       in
                                    FStar_Syntax_Util.mk_conj uu____12195
                                      impl
                                     in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl  in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12201;
                     FStar_Syntax_Syntax.tk = uu____12202;
                     FStar_Syntax_Syntax.pos = uu____12203;
                     FStar_Syntax_Syntax.vars = uu____12204;_},uu____12205),uu____12206)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation
                         in
                      let uu____12231 =
                        let uu____12232 = is_top_level_prob orig  in
                        FStar_All.pipe_left Prims.op_Negation uu____12232  in
                      if uu____12231
                      then
                        let uu____12233 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___170_12236 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_12236.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_12236.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_12236.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_12236.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_12236.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_12236.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_12236.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_12236.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_12236.FStar_TypeChecker_Common.rank)
                             })
                           in
                        let uu____12237 = destruct_flex_pattern env t1  in
                        solve_t_flex_rigid false uu____12233 uu____12237 t2
                          wl
                      else
                        (let uu____12242 = base_and_refinement env wl t2  in
                         match uu____12242 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12272 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___171_12275 = problem  in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_12275.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_12275.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_12275.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_12275.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_12275.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_12275.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_12275.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_12275.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_12275.FStar_TypeChecker_Common.rank)
                                       })
                                     in
                                  let uu____12276 =
                                    destruct_flex_pattern env t1  in
                                  solve_t_flex_rigid false uu____12272
                                    uu____12276 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___172_12291 = y  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_12291.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_12291.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }  in
                                  let impl =
                                    guard_on_element wl problem y' phi  in
                                  let base_prob =
                                    let uu____12294 =
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
                                      uu____12294
                                     in
                                  let guard =
                                    let uu____12302 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst
                                       in
                                    FStar_Syntax_Util.mk_conj uu____12302
                                      impl
                                     in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl  in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____12308,FStar_Syntax_Syntax.Tm_uvar uu____12309) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12319 = base_and_refinement env wl t1  in
                      match uu____12319 with
                      | (t_base,uu____12330) ->
                          solve_t env
                            (let uu___173_12345 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_12345.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_12345.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_12345.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_12345.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_12345.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_12345.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_12345.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_12345.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____12348,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12349;
                     FStar_Syntax_Syntax.tk = uu____12350;
                     FStar_Syntax_Syntax.pos = uu____12351;
                     FStar_Syntax_Syntax.vars = uu____12352;_},uu____12353))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12377 = base_and_refinement env wl t1  in
                      match uu____12377 with
                      | (t_base,uu____12388) ->
                          solve_t env
                            (let uu___173_12403 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_12403.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_12403.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_12403.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_12403.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_12403.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_12403.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_12403.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_12403.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____12406,uu____12407) ->
                   let t21 =
                     let uu____12415 = base_and_refinement env wl t2  in
                     FStar_All.pipe_left force_refinement uu____12415  in
                   solve_t env
                     (let uu___174_12428 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_12428.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___174_12428.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___174_12428.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___174_12428.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_12428.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_12428.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_12428.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_12428.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_12428.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12429,FStar_Syntax_Syntax.Tm_refine uu____12430) ->
                   let t11 =
                     let uu____12438 = base_and_refinement env wl t1  in
                     FStar_All.pipe_left force_refinement uu____12438  in
                   solve_t env
                     (let uu___175_12451 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_12451.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___175_12451.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___175_12451.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___175_12451.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_12451.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_12451.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_12451.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_12451.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_12451.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12454,uu____12455) ->
                   let head1 =
                     let uu____12474 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12474 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12505 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12505 FStar_Pervasives.fst
                      in
                   let uu____12533 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12533
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12542 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12542
                      then
                        let guard =
                          let uu____12549 =
                            let uu____12550 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12550 = FStar_Syntax_Util.Equal  in
                          if uu____12549
                          then None
                          else
                            (let uu____12553 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_76  -> Some _0_76)
                               uu____12553)
                           in
                        let uu____12555 = solve_prob orig guard [] wl  in
                        solve env uu____12555
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12558,uu____12559) ->
                   let head1 =
                     let uu____12567 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12567 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12598 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12598 FStar_Pervasives.fst
                      in
                   let uu____12626 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12626
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12635 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12635
                      then
                        let guard =
                          let uu____12642 =
                            let uu____12643 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12643 = FStar_Syntax_Util.Equal  in
                          if uu____12642
                          then None
                          else
                            (let uu____12646 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_77  -> Some _0_77)
                               uu____12646)
                           in
                        let uu____12648 = solve_prob orig guard [] wl  in
                        solve env uu____12648
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12651,uu____12652) ->
                   let head1 =
                     let uu____12656 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12656 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12687 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12687 FStar_Pervasives.fst
                      in
                   let uu____12715 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12715
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12724 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12724
                      then
                        let guard =
                          let uu____12731 =
                            let uu____12732 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12732 = FStar_Syntax_Util.Equal  in
                          if uu____12731
                          then None
                          else
                            (let uu____12735 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_78  -> Some _0_78)
                               uu____12735)
                           in
                        let uu____12737 = solve_prob orig guard [] wl  in
                        solve env uu____12737
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____12740,uu____12741) ->
                   let head1 =
                     let uu____12745 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12745 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12776 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12776 FStar_Pervasives.fst
                      in
                   let uu____12804 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12804
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12813 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12813
                      then
                        let guard =
                          let uu____12820 =
                            let uu____12821 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12821 = FStar_Syntax_Util.Equal  in
                          if uu____12820
                          then None
                          else
                            (let uu____12824 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_79  -> Some _0_79)
                               uu____12824)
                           in
                        let uu____12826 = solve_prob orig guard [] wl  in
                        solve env uu____12826
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____12829,uu____12830) ->
                   let head1 =
                     let uu____12834 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12834 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12865 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12865 FStar_Pervasives.fst
                      in
                   let uu____12893 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12893
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12902 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12902
                      then
                        let guard =
                          let uu____12909 =
                            let uu____12910 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12910 = FStar_Syntax_Util.Equal  in
                          if uu____12909
                          then None
                          else
                            (let uu____12913 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_80  -> Some _0_80)
                               uu____12913)
                           in
                        let uu____12915 = solve_prob orig guard [] wl  in
                        solve env uu____12915
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____12918,uu____12919) ->
                   let head1 =
                     let uu____12932 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12932 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12963 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12963 FStar_Pervasives.fst
                      in
                   let uu____12991 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12991
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13000 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13000
                      then
                        let guard =
                          let uu____13007 =
                            let uu____13008 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13008 = FStar_Syntax_Util.Equal  in
                          if uu____13007
                          then None
                          else
                            (let uu____13011 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_81  -> Some _0_81)
                               uu____13011)
                           in
                        let uu____13013 = solve_prob orig guard [] wl  in
                        solve env uu____13013
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13016,FStar_Syntax_Syntax.Tm_match uu____13017) ->
                   let head1 =
                     let uu____13036 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13036 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____13067 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13067 FStar_Pervasives.fst
                      in
                   let uu____13095 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13095
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13104 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13104
                      then
                        let guard =
                          let uu____13111 =
                            let uu____13112 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13112 = FStar_Syntax_Util.Equal  in
                          if uu____13111
                          then None
                          else
                            (let uu____13115 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_82  -> Some _0_82)
                               uu____13115)
                           in
                        let uu____13117 = solve_prob orig guard [] wl  in
                        solve env uu____13117
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13120,FStar_Syntax_Syntax.Tm_uinst uu____13121) ->
                   let head1 =
                     let uu____13129 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13129 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____13160 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13160 FStar_Pervasives.fst
                      in
                   let uu____13188 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13188
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13197 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13197
                      then
                        let guard =
                          let uu____13204 =
                            let uu____13205 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13205 = FStar_Syntax_Util.Equal  in
                          if uu____13204
                          then None
                          else
                            (let uu____13208 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_83  -> Some _0_83)
                               uu____13208)
                           in
                        let uu____13210 = solve_prob orig guard [] wl  in
                        solve env uu____13210
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13213,FStar_Syntax_Syntax.Tm_name uu____13214) ->
                   let head1 =
                     let uu____13218 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13218 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____13249 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13249 FStar_Pervasives.fst
                      in
                   let uu____13277 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13277
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13286 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13286
                      then
                        let guard =
                          let uu____13293 =
                            let uu____13294 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13294 = FStar_Syntax_Util.Equal  in
                          if uu____13293
                          then None
                          else
                            (let uu____13297 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_84  -> Some _0_84)
                               uu____13297)
                           in
                        let uu____13299 = solve_prob orig guard [] wl  in
                        solve env uu____13299
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13302,FStar_Syntax_Syntax.Tm_constant uu____13303) ->
                   let head1 =
                     let uu____13307 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13307 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____13338 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13338 FStar_Pervasives.fst
                      in
                   let uu____13366 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13366
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13375 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13375
                      then
                        let guard =
                          let uu____13382 =
                            let uu____13383 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13383 = FStar_Syntax_Util.Equal  in
                          if uu____13382
                          then None
                          else
                            (let uu____13386 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_85  -> Some _0_85)
                               uu____13386)
                           in
                        let uu____13388 = solve_prob orig guard [] wl  in
                        solve env uu____13388
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13391,FStar_Syntax_Syntax.Tm_fvar uu____13392) ->
                   let head1 =
                     let uu____13396 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13396 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____13427 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13427 FStar_Pervasives.fst
                      in
                   let uu____13455 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13455
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13464 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13464
                      then
                        let guard =
                          let uu____13471 =
                            let uu____13472 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13472 = FStar_Syntax_Util.Equal  in
                          if uu____13471
                          then None
                          else
                            (let uu____13475 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_86  -> Some _0_86)
                               uu____13475)
                           in
                        let uu____13477 = solve_prob orig guard [] wl  in
                        solve env uu____13477
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13480,FStar_Syntax_Syntax.Tm_app uu____13481) ->
                   let head1 =
                     let uu____13494 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13494 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____13525 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13525 FStar_Pervasives.fst
                      in
                   let uu____13553 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13553
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13562 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13562
                      then
                        let guard =
                          let uu____13569 =
                            let uu____13570 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13570 = FStar_Syntax_Util.Equal  in
                          if uu____13569
                          then None
                          else
                            (let uu____13573 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_87  -> Some _0_87)
                               uu____13573)
                           in
                        let uu____13575 = solve_prob orig guard [] wl  in
                        solve env uu____13575
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____13579,uu____13580),uu____13581) ->
                   solve_t' env
                     (let uu___176_13610 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_13610.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___176_13610.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___176_13610.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___176_13610.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_13610.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_13610.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_13610.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_13610.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_13610.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____13613,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____13615,uu____13616)) ->
                   solve_t' env
                     (let uu___177_13645 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___177_13645.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___177_13645.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___177_13645.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___177_13645.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___177_13645.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___177_13645.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___177_13645.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___177_13645.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___177_13645.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____13646,uu____13647) ->
                   let uu____13655 =
                     let uu____13656 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13657 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13656
                       uu____13657
                      in
                   failwith uu____13655
               | (FStar_Syntax_Syntax.Tm_meta uu____13658,uu____13659) ->
                   let uu____13664 =
                     let uu____13665 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13666 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13665
                       uu____13666
                      in
                   failwith uu____13664
               | (FStar_Syntax_Syntax.Tm_delayed uu____13667,uu____13668) ->
                   let uu____13683 =
                     let uu____13684 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13685 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13684
                       uu____13685
                      in
                   failwith uu____13683
               | (uu____13686,FStar_Syntax_Syntax.Tm_meta uu____13687) ->
                   let uu____13692 =
                     let uu____13693 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13694 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13693
                       uu____13694
                      in
                   failwith uu____13692
               | (uu____13695,FStar_Syntax_Syntax.Tm_delayed uu____13696) ->
                   let uu____13711 =
                     let uu____13712 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13713 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13712
                       uu____13713
                      in
                   failwith uu____13711
               | (uu____13714,FStar_Syntax_Syntax.Tm_let uu____13715) ->
                   let uu____13723 =
                     let uu____13724 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13725 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13724
                       uu____13725
                      in
                   failwith uu____13723
               | uu____13726 -> giveup env "head tag mismatch" orig)))

and solve_c :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem ->
      worklist -> solution
  =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let c1 = problem.FStar_TypeChecker_Common.lhs  in
        let c2 = problem.FStar_TypeChecker_Common.rhs  in
        let orig = FStar_TypeChecker_Common.CProb problem  in
        let sub_prob t1 rel t2 reason =
          mk_problem (p_scope orig) orig t1 rel t2 None reason  in
        let solve_eq c1_comp c2_comp =
          (let uu____13758 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____13758
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____13766  ->
                  fun uu____13767  ->
                    match (uu____13766, uu____13767) with
                    | ((a1,uu____13777),(a2,uu____13779)) ->
                        let uu____13784 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg"
                           in
                        FStar_All.pipe_left
                          (fun _0_88  -> FStar_TypeChecker_Common.TProb _0_88)
                          uu____13784)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args
              in
           let guard =
             let uu____13790 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p) FStar_Pervasives.fst)
                 sub_probs
                in
             FStar_Syntax_Util.mk_conj_l uu____13790  in
           let wl1 = solve_prob orig (Some guard) [] wl  in
           solve env (attempt sub_probs wl1))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____13810 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____13817)::[] -> wp1
              | uu____13830 ->
                  let uu____13836 =
                    let uu____13837 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name)
                       in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____13837
                     in
                  failwith uu____13836
               in
            let uu____13840 =
              let uu____13846 =
                let uu____13847 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____13847  in
              [uu____13846]  in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____13840;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____13848 = lift_c1 ()  in solve_eq uu____13848 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___134_13852  ->
                       match uu___134_13852 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____13853 -> false))
                in
             let uu____13854 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____13878)::uu____13879,(wp2,uu____13881)::uu____13882)
                   -> (wp1, wp2)
               | uu____13923 ->
                   let uu____13936 =
                     let uu____13937 =
                       let uu____13940 =
                         let uu____13941 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____13942 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____13941 uu____13942
                          in
                       (uu____13940, (env.FStar_TypeChecker_Env.range))  in
                     FStar_Errors.Error uu____13937  in
                   raise uu____13936
                in
             match uu____13854 with
             | (wpc1,wpc2) ->
                 let uu____13959 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____13959
                 then
                   let uu____13962 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type"
                      in
                   solve_t env uu____13962 wl
                 else
                   (let uu____13966 =
                      let uu____13970 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____13970  in
                    match uu____13966 with
                    | (c2_decl,qualifiers) ->
                        let uu____13982 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____13982
                        then
                          let c1_repr =
                            let uu____13985 =
                              let uu____13986 =
                                let uu____13987 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____13987  in
                              let uu____13988 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____13986 uu____13988
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____13985
                             in
                          let c2_repr =
                            let uu____13990 =
                              let uu____13991 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____13992 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____13991 uu____13992
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____13990
                             in
                          let prob =
                            let uu____13994 =
                              let uu____13997 =
                                let uu____13998 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____13999 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____13998
                                  uu____13999
                                 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____13997
                               in
                            FStar_TypeChecker_Common.TProb uu____13994  in
                          let wl1 =
                            let uu____14001 =
                              let uu____14003 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives.fst
                                 in
                              Some uu____14003  in
                            solve_prob orig uu____14001 [] wl  in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____14010 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____14010
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____14012 =
                                     let uu____14015 =
                                       let uu____14016 =
                                         let uu____14026 =
                                           let uu____14027 =
                                             let uu____14028 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ
                                                in
                                             [uu____14028]  in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____14027 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____14029 =
                                           let uu____14031 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____14032 =
                                             let uu____14034 =
                                               let uu____14035 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____14035
                                                in
                                             [uu____14034]  in
                                           uu____14031 :: uu____14032  in
                                         (uu____14026, uu____14029)  in
                                       FStar_Syntax_Syntax.Tm_app uu____14016
                                        in
                                     FStar_Syntax_Syntax.mk uu____14015  in
                                   uu____14012
                                     (Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____14046 =
                                    let uu____14049 =
                                      let uu____14050 =
                                        let uu____14060 =
                                          let uu____14061 =
                                            let uu____14062 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ
                                               in
                                            [uu____14062]  in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____14061 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____14063 =
                                          let uu____14065 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____14066 =
                                            let uu____14068 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____14069 =
                                              let uu____14071 =
                                                let uu____14072 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____14072
                                                 in
                                              [uu____14071]  in
                                            uu____14068 :: uu____14069  in
                                          uu____14065 :: uu____14066  in
                                        (uu____14060, uu____14063)  in
                                      FStar_Syntax_Syntax.Tm_app uu____14050
                                       in
                                    FStar_Syntax_Syntax.mk uu____14049  in
                                  uu____14046
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r)
                              in
                           let base_prob =
                             let uu____14083 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type"
                                in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____14083
                              in
                           let wl1 =
                             let uu____14089 =
                               let uu____14091 =
                                 let uu____14094 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____14094 g  in
                               FStar_All.pipe_left (fun _0_90  -> Some _0_90)
                                 uu____14091
                                in
                             solve_prob orig uu____14089 [] wl  in
                           solve env (attempt [base_prob] wl1))))
           in
        let uu____14104 = FStar_Util.physical_equality c1 c2  in
        if uu____14104
        then
          let uu____14105 = solve_prob orig None [] wl  in
          solve env uu____14105
        else
          ((let uu____14108 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____14108
            then
              let uu____14109 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____14110 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____14109
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____14110
            else ());
           (let uu____14112 =
              let uu____14115 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____14116 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____14115, uu____14116)  in
            match uu____14112 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14120),FStar_Syntax_Syntax.Total
                    (t2,uu____14122)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____14135 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type"
                        in
                     solve_t env uu____14135 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14138,FStar_Syntax_Syntax.Total uu____14139) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14151),FStar_Syntax_Syntax.Total
                    (t2,uu____14153)) ->
                     let uu____14166 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type"
                        in
                     solve_t env uu____14166 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14170),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14172)) ->
                     let uu____14185 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type"
                        in
                     solve_t env uu____14185 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14189),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14191)) ->
                     let uu____14204 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type"
                        in
                     solve_t env uu____14204 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14207,FStar_Syntax_Syntax.Comp uu____14208) ->
                     let uu____14214 =
                       let uu___178_14217 = problem  in
                       let uu____14220 =
                         let uu____14221 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14221
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14217.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14220;
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14217.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___178_14217.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___178_14217.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14217.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14217.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14217.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14217.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14217.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____14214 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____14222,FStar_Syntax_Syntax.Comp uu____14223) ->
                     let uu____14229 =
                       let uu___178_14232 = problem  in
                       let uu____14235 =
                         let uu____14236 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14236
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_14232.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14235;
                         FStar_TypeChecker_Common.relation =
                           (uu___178_14232.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___178_14232.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___178_14232.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_14232.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_14232.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_14232.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_14232.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_14232.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____14229 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14237,FStar_Syntax_Syntax.GTotal uu____14238) ->
                     let uu____14244 =
                       let uu___179_14247 = problem  in
                       let uu____14250 =
                         let uu____14251 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14251
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___179_14247.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___179_14247.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___179_14247.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14250;
                         FStar_TypeChecker_Common.element =
                           (uu___179_14247.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___179_14247.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___179_14247.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___179_14247.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___179_14247.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___179_14247.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____14244 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14252,FStar_Syntax_Syntax.Total uu____14253) ->
                     let uu____14259 =
                       let uu___179_14262 = problem  in
                       let uu____14265 =
                         let uu____14266 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14266
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___179_14262.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___179_14262.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___179_14262.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14265;
                         FStar_TypeChecker_Common.element =
                           (uu___179_14262.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___179_14262.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___179_14262.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___179_14262.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___179_14262.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___179_14262.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____14259 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14267,FStar_Syntax_Syntax.Comp uu____14268) ->
                     let uu____14269 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21)))
                        in
                     if uu____14269
                     then
                       let uu____14270 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type"
                          in
                       solve_t env uu____14270 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            &&
                            (FStar_Ident.lid_equals
                               c1_comp.FStar_Syntax_Syntax.effect_name
                               c2_comp.FStar_Syntax_Syntax.effect_name)
                        then solve_eq c1_comp c2_comp
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11
                              in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21
                              in
                           (let uu____14280 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____14280
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____14282 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____14282 with
                            | None  ->
                                let uu____14284 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____14285 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ
                                        in
                                     FStar_Syntax_Util.non_informative
                                       uu____14285)
                                   in
                                if uu____14284
                                then
                                  let edge =
                                    {
                                      FStar_TypeChecker_Env.msource =
                                        (c12.FStar_Syntax_Syntax.effect_name);
                                      FStar_TypeChecker_Env.mtarget =
                                        (c22.FStar_Syntax_Syntax.effect_name);
                                      FStar_TypeChecker_Env.mlift =
                                        FStar_TypeChecker_Env.identity_mlift
                                    }  in
                                  solve_sub c12 edge c22
                                else
                                  (let uu____14288 =
                                     let uu____14289 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name
                                        in
                                     let uu____14290 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name
                                        in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____14289 uu____14290
                                      in
                                   giveup env uu____14288 orig)
                            | Some edge -> solve_sub c12 edge c22))))))

let print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____14296 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____14312  ->
              match uu____14312 with
              | (uu____14319,uu____14320,u,uu____14322,uu____14323,uu____14324)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____14296 (FStar_String.concat ", ")
  
let ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____14343 =
        FStar_All.pipe_right (fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____14343 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____14353 =
        FStar_All.pipe_right (snd ineqs)
          (FStar_List.map
             (fun uu____14365  ->
                match uu____14365 with
                | (u1,u2) ->
                    let uu____14370 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____14371 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____14370 uu____14371))
         in
      FStar_All.pipe_right uu____14353 (FStar_String.concat ", ")  in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1
  
let guard_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.string
  =
  fun env  ->
    fun g  ->
      match ((g.FStar_TypeChecker_Env.guard_f),
              (g.FStar_TypeChecker_Env.deferred),
              (g.FStar_TypeChecker_Env.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____14385,[])) -> "{}"
      | uu____14398 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____14408 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____14408
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____14411 =
              FStar_List.map
                (fun uu____14415  ->
                   match uu____14415 with
                   | (uu____14418,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____14411 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____14422 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____14422 imps
  
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14467 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel")
       in
    if uu____14467
    then
      let uu____14468 = FStar_TypeChecker_Normalize.term_to_string env lhs
         in
      let uu____14469 = FStar_TypeChecker_Normalize.term_to_string env rhs
         in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14468
        (rel_to_string rel) uu____14469
    else "TOP"  in
  let p = new_problem env lhs rel rhs elt loc reason  in p 
let new_t_prob :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Common.rel ->
        FStar_Syntax_Syntax.term ->
          (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv)
  =
  fun env  ->
    fun t1  ->
      fun rel  ->
        fun t2  ->
          let x =
            let uu____14493 =
              let uu____14495 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left (fun _0_91  -> Some _0_91) uu____14495  in
            FStar_Syntax_Syntax.new_bv uu____14493 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____14501 =
              let uu____14503 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left (fun _0_92  -> Some _0_92) uu____14503  in
            let uu____14505 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____14501 uu____14505  in
          ((FStar_TypeChecker_Common.TProb p), x)
  
let solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob * Prims.string) ->
         FStar_TypeChecker_Common.deferred option)
        -> FStar_TypeChecker_Common.deferred option
  =
  fun env  ->
    fun probs  ->
      fun err1  ->
        let probs1 =
          let uu____14531 = FStar_Options.eager_inference ()  in
          if uu____14531
          then
            let uu___180_14532 = probs  in
            {
              attempting = (uu___180_14532.attempting);
              wl_deferred = (uu___180_14532.wl_deferred);
              ctr = (uu___180_14532.ctr);
              defer_ok = false;
              smt_ok = (uu___180_14532.smt_ok);
              tcenv = (uu___180_14532.tcenv)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Syntax_Unionfind.rollback tx;
             (let uu____14543 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____14543
              then
                let uu____14544 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____14544
              else ());
             err1 (d, s))
  
let simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____14556 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____14556
            then
              let uu____14557 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14557
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops] env f
               in
            (let uu____14561 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____14561
             then
               let uu____14562 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14562
             else ());
            (let f2 =
               let uu____14565 =
                 let uu____14566 = FStar_Syntax_Util.unmeta f1  in
                 uu____14566.FStar_Syntax_Syntax.n  in
               match uu____14565 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14570 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___181_14571 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___181_14571.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___181_14571.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___181_14571.FStar_TypeChecker_Env.implicits)
             })))
  
let with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_TypeChecker_Common.deferred option ->
        FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | None  -> None
        | Some d ->
            let uu____14589 =
              let uu____14590 =
                let uu____14591 =
                  let uu____14592 =
                    FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst
                     in
                  FStar_All.pipe_right uu____14592
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14591;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____14590  in
            FStar_All.pipe_left (fun _0_94  -> Some _0_94) uu____14589
  
let with_guard_no_simp env prob dopt =
  match dopt with
  | None  -> None
  | Some d ->
      let uu____14629 =
        let uu____14630 =
          let uu____14631 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst  in
          FStar_All.pipe_right uu____14631
            (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95)
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____14630;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        }  in
      Some uu____14629
  
let try_teq :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t option
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____14661 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____14661
           then
             let uu____14662 = FStar_Syntax_Print.term_to_string t1  in
             let uu____14663 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14662
               uu____14663
           else ());
          (let prob =
             let uu____14666 =
               let uu____14669 = FStar_TypeChecker_Env.get_range env  in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____14669
                in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____14666
              in
           let g =
             let uu____14674 =
               let uu____14676 = singleton' env prob smt_ok  in
               solve_and_commit env uu____14676 (fun uu____14677  -> None)
                in
             FStar_All.pipe_left (with_guard env prob) uu____14674  in
           g)
  
let teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14694 = try_teq true env t1 t2  in
        match uu____14694 with
        | None  ->
            let uu____14696 =
              let uu____14697 =
                let uu____14700 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1  in
                let uu____14701 = FStar_TypeChecker_Env.get_range env  in
                (uu____14700, uu____14701)  in
              FStar_Errors.Error uu____14697  in
            raise uu____14696
        | Some g ->
            ((let uu____14704 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____14704
              then
                let uu____14705 = FStar_Syntax_Print.term_to_string t1  in
                let uu____14706 = FStar_Syntax_Print.term_to_string t2  in
                let uu____14707 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____14705
                  uu____14706 uu____14707
              else ());
             g)
  
let try_subtype' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        Prims.bool -> FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        fun smt_ok  ->
          (let uu____14727 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____14727
           then
             let uu____14728 =
               FStar_TypeChecker_Normalize.term_to_string env t1  in
             let uu____14729 =
               FStar_TypeChecker_Normalize.term_to_string env t2  in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____14728
               uu____14729
           else ());
          (let uu____14731 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2  in
           match uu____14731 with
           | (prob,x) ->
               let g =
                 let uu____14739 =
                   let uu____14741 = singleton' env prob smt_ok  in
                   solve_and_commit env uu____14741
                     (fun uu____14742  -> None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____14739  in
               ((let uu____14748 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g)
                    in
                 if uu____14748
                 then
                   let uu____14749 =
                     FStar_TypeChecker_Normalize.term_to_string env t1  in
                   let uu____14750 =
                     FStar_TypeChecker_Normalize.term_to_string env t2  in
                   let uu____14751 =
                     let uu____14752 = FStar_Util.must g  in
                     guard_to_string env uu____14752  in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____14749 uu____14750 uu____14751
                 else ());
                abstract_guard x g))
  
let try_subtype :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t option
  = fun env  -> fun t1  -> fun t2  -> try_subtype' env t1 t2 true 
let subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.unit
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____14783 = FStar_TypeChecker_Env.get_range env  in
          let uu____14784 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1  in
          FStar_Errors.err uu____14783 uu____14784
  
let sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____14799 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____14799
         then
           let uu____14800 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____14801 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____14800
             uu____14801
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB  in
         let prob =
           let uu____14806 =
             let uu____14809 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 None uu____14809 "sub_comp"  in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____14806
            in
         let uu____14812 =
           let uu____14814 = singleton env prob  in
           solve_and_commit env uu____14814 (fun uu____14815  -> None)  in
         FStar_All.pipe_left (with_guard env prob) uu____14812)
  
let solve_universe_inequalities' :
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list *
        (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____14837  ->
        match uu____14837 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____14862 =
                 let uu____14863 =
                   let uu____14866 =
                     let uu____14867 = FStar_Syntax_Print.univ_to_string u1
                        in
                     let uu____14868 = FStar_Syntax_Print.univ_to_string u2
                        in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____14867 uu____14868
                      in
                   let uu____14869 = FStar_TypeChecker_Env.get_range env  in
                   (uu____14866, uu____14869)  in
                 FStar_Errors.Error uu____14863  in
               raise uu____14862)
               in
            let equiv1 v1 v' =
              let uu____14877 =
                let uu____14880 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____14881 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____14880, uu____14881)  in
              match uu____14877 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____14888 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____14902 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____14902 with
                      | FStar_Syntax_Syntax.U_unif uu____14906 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____14917  ->
                                    match uu____14917 with
                                    | (u,v') ->
                                        let uu____14923 = equiv1 v1 v'  in
                                        if uu____14923
                                        then
                                          let uu____14925 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____14925 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____14935 -> []))
               in
            let uu____14938 =
              let wl =
                let uu___182_14941 = empty_worklist env  in
                {
                  attempting = (uu___182_14941.attempting);
                  wl_deferred = (uu___182_14941.wl_deferred);
                  ctr = (uu___182_14941.ctr);
                  defer_ok = false;
                  smt_ok = (uu___182_14941.smt_ok);
                  tcenv = (uu___182_14941.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____14948  ->
                      match uu____14948 with
                      | (lb,v1) ->
                          let uu____14953 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____14953 with
                           | USolved wl1 -> ()
                           | uu____14955 -> fail lb v1)))
               in
            let rec check_ineq uu____14961 =
              match uu____14961 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____14968) -> true
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
                      uu____14979,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____14981,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____14986) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____14990,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____14995 -> false)
               in
            let uu____14998 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____15004  ->
                      match uu____15004 with
                      | (u,v1) ->
                          let uu____15009 = check_ineq (u, v1)  in
                          if uu____15009
                          then true
                          else
                            ((let uu____15012 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____15012
                              then
                                let uu____15013 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____15014 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____15013
                                  uu____15014
                              else ());
                             false)))
               in
            if uu____14998
            then ()
            else
              ((let uu____15018 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____15018
                then
                  ((let uu____15020 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____15020);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____15026 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____15026))
                else ());
               (let uu____15032 =
                  let uu____15033 =
                    let uu____15036 = FStar_TypeChecker_Env.get_range env  in
                    ("Failed to solve universe inequalities for inductives",
                      uu____15036)
                     in
                  FStar_Errors.Error uu____15033  in
                raise uu____15032))
  
let solve_universe_inequalities :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe
      * FStar_Syntax_Syntax.universe) Prims.list) -> Prims.unit
  =
  fun env  ->
    fun ineqs  ->
      let tx = FStar_Syntax_Unionfind.new_transaction ()  in
      solve_universe_inequalities' tx env ineqs;
      FStar_Syntax_Unionfind.commit tx
  
let rec solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let fail uu____15073 =
        match uu____15073 with
        | (d,s) ->
            let msg = explain env d s  in
            raise (FStar_Errors.Error (msg, (p_loc d)))
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____15083 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____15083
       then
         let uu____15084 = wl_to_string wl  in
         let uu____15085 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits)
            in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____15084 uu____15085
       else ());
      (let g1 =
         let uu____15100 = solve_and_commit env wl fail  in
         match uu____15100 with
         | Some [] ->
             let uu___183_15107 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___183_15107.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___183_15107.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___183_15107.FStar_TypeChecker_Env.implicits)
             }
         | uu____15110 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___184_15113 = g1  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___184_15113.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___184_15113.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___184_15113.FStar_TypeChecker_Env.implicits)
        }))
  
let discharge_guard' :
  (Prims.unit -> Prims.string) option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t ->
        Prims.bool -> FStar_TypeChecker_Env.guard_t option
  =
  fun use_env_range_msg  ->
    fun env  ->
      fun g  ->
        fun use_smt  ->
          let g1 = solve_deferred_constraints env g  in
          let ret_g =
            let uu___185_15143 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___185_15143.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___185_15143.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___185_15143.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____15144 =
            let uu____15145 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____15145  in
          if uu____15144
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____15151 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery"))
                      in
                   if uu____15151
                   then
                     let uu____15152 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____15153 =
                       let uu____15154 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____15154
                        in
                     FStar_Errors.diag uu____15152 uu____15153
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   let uu____15157 = check_trivial vc1  in
                   match uu____15157 with
                   | FStar_TypeChecker_Common.Trivial  -> Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then
                         ((let uu____15162 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____15162
                           then
                             let uu____15163 =
                               FStar_TypeChecker_Env.get_range env  in
                             let uu____15164 =
                               let uu____15165 =
                                 FStar_Syntax_Print.term_to_string vc2  in
                               FStar_Util.format1
                                 "Cannot solve without SMT : %s\n"
                                 uu____15165
                                in
                             FStar_Errors.diag uu____15163 uu____15164
                           else ());
                          None)
                       else
                         ((let uu____15170 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____15170
                           then
                             let uu____15171 =
                               FStar_TypeChecker_Env.get_range env  in
                             let uu____15172 =
                               let uu____15173 =
                                 FStar_Syntax_Print.term_to_string vc2  in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____15173
                                in
                             FStar_Errors.diag uu____15171 uu____15172
                           else ());
                          (let vcs =
                             let uu____15180 = FStar_Options.use_tactics ()
                                in
                             if uu____15180
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else
                               (let uu____15186 =
                                  let uu____15190 = FStar_Options.peek ()  in
                                  (env, vc2, uu____15190)  in
                                [uu____15186])
                              in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____15204  ->
                                   match uu____15204 with
                                   | (env1,goal,opts) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify;
                                           FStar_TypeChecker_Normalize.Primops]
                                           env1 goal
                                          in
                                       let uu____15212 = check_trivial goal1
                                          in
                                       (match uu____15212 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____15214 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac"))
                                               in
                                            if uu____15214
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            (FStar_Options.push ();
                                             FStar_Options.set opts;
                                             (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                                               ();
                                             (let uu____15221 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel")
                                                 in
                                              if uu____15221
                                              then
                                                let uu____15222 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1
                                                   in
                                                let uu____15223 =
                                                  let uu____15224 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2
                                                     in
                                                  let uu____15225 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1
                                                     in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____15224 uu____15225
                                                   in
                                                FStar_Errors.diag uu____15222
                                                  uu____15223
                                              else ());
                                             (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                               use_env_range_msg env1 goal2;
                                             FStar_Options.pop ())))));
                          Some ret_g))))
  
let discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15237 = discharge_guard' None env g false  in
      match uu____15237 with
      | Some g1 -> g1
      | None  ->
          let uu____15242 =
            let uu____15243 =
              let uu____15246 = FStar_TypeChecker_Env.get_range env  in
              ("Expected a trivial pre-condition", uu____15246)  in
            FStar_Errors.Error uu____15243  in
          raise uu____15242
  
let discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15255 = discharge_guard' None env g true  in
      match uu____15255 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let resolve_implicits' :
  Prims.bool ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun forcelax  ->
    fun g  ->
      let unresolved u =
        let uu____15272 = FStar_Syntax_Unionfind.find u  in
        match uu____15272 with | None  -> true | uu____15274 -> false  in
      let rec until_fixpoint acc implicits =
        let uu____15287 = acc  in
        match uu____15287 with
        | (out,changed) ->
            (match implicits with
             | [] ->
                 if Prims.op_Negation changed
                 then out
                 else until_fixpoint ([], false) out
             | hd1::tl1 ->
                 let uu____15333 = hd1  in
                 (match uu____15333 with
                  | (uu____15340,env,u,tm,k,r) ->
                      let uu____15346 = unresolved u  in
                      if uu____15346
                      then until_fixpoint ((hd1 :: out), changed) tl1
                      else
                        (let env1 =
                           FStar_TypeChecker_Env.set_expected_typ env k  in
                         let tm1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta] env1 tm
                            in
                         (let uu____15364 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "RelCheck")
                             in
                          if uu____15364
                          then
                            let uu____15365 =
                              FStar_Syntax_Print.uvar_to_string u  in
                            let uu____15366 =
                              FStar_Syntax_Print.term_to_string tm1  in
                            let uu____15367 =
                              FStar_Syntax_Print.term_to_string k  in
                            FStar_Util.print3
                              "Checking uvar %s resolved to %s at type %s\n"
                              uu____15365 uu____15366 uu____15367
                          else ());
                         (let env2 =
                            if forcelax
                            then
                              let uu___186_15370 = env1  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___186_15370.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___186_15370.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___186_15370.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___186_15370.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___186_15370.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___186_15370.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___186_15370.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___186_15370.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___186_15370.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___186_15370.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___186_15370.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___186_15370.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___186_15370.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___186_15370.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___186_15370.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___186_15370.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___186_15370.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___186_15370.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___186_15370.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___186_15370.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___186_15370.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___186_15370.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___186_15370.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___186_15370.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___186_15370.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___186_15370.FStar_TypeChecker_Env.is_native_tactic)
                              }
                            else env1  in
                          let uu____15372 =
                            env2.FStar_TypeChecker_Env.type_of
                              (let uu___187_15376 = env2  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___187_15376.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___187_15376.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___187_15376.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___187_15376.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___187_15376.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___187_15376.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___187_15376.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___187_15376.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___187_15376.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___187_15376.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___187_15376.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___187_15376.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___187_15376.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___187_15376.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___187_15376.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___187_15376.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___187_15376.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___187_15376.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___187_15376.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___187_15376.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___187_15376.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___187_15376.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___187_15376.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___187_15376.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___187_15376.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___187_15376.FStar_TypeChecker_Env.is_native_tactic)
                               }) tm1
                             in
                          match uu____15372 with
                          | (uu____15377,uu____15378,g1) ->
                              let g2 =
                                if env2.FStar_TypeChecker_Env.is_pattern
                                then
                                  let uu___188_15381 = g1  in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      FStar_TypeChecker_Common.Trivial;
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___188_15381.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___188_15381.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits =
                                      (uu___188_15381.FStar_TypeChecker_Env.implicits)
                                  }
                                else g1  in
                              let g' =
                                let uu____15384 =
                                  discharge_guard'
                                    (Some
                                       (fun uu____15388  ->
                                          FStar_Syntax_Print.term_to_string
                                            tm1)) env2 g2 true
                                   in
                                match uu____15384 with
                                | Some g3 -> g3
                                | None  ->
                                    failwith
                                      "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                                 in
                              until_fixpoint
                                ((FStar_List.append
                                    g'.FStar_TypeChecker_Env.implicits out),
                                  true) tl1))))
         in
      let uu___189_15403 = g  in
      let uu____15404 =
        until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___189_15403.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___189_15403.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs =
          (uu___189_15403.FStar_TypeChecker_Env.univ_ineqs);
        FStar_TypeChecker_Env.implicits = uu____15404
      }
  
let resolve_implicits :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  -> resolve_implicits' false g 
let resolve_implicits_lax :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  -> resolve_implicits' true g 
let force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____15442 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____15442 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____15449 = discharge_guard env g1  in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____15449
      | (reason,uu____15451,uu____15452,e,t,r)::uu____15456 ->
          let uu____15470 =
            let uu____15471 = FStar_Syntax_Print.term_to_string t  in
            let uu____15472 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2
              "Failed to resolve implicit argument of type '%s' introduced in %s"
              uu____15471 uu____15472
             in
          FStar_Errors.err r uu____15470
  
let universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___190_15481 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___190_15481.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___190_15481.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___190_15481.FStar_TypeChecker_Env.implicits)
      }
  
let teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15502 = try_teq false env t1 t2  in
        match uu____15502 with
        | None  -> false
        | Some g ->
            let uu____15505 = discharge_guard' None env g false  in
            (match uu____15505 with
             | Some uu____15509 -> true
             | None  -> false)
  