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
        FStar_TypeChecker_Env.univ_ineqs = uu____20;
        FStar_TypeChecker_Env.implicits = uu____21;_} -> true
    | uu____35 -> false
  
let trivial_guard : FStar_TypeChecker_Env.guard_t =
  {
    FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial;
    FStar_TypeChecker_Env.deferred = [];
    FStar_TypeChecker_Env.univ_ineqs = ([], []);
    FStar_TypeChecker_Env.implicits = []
  } 
let abstract_guard :
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.guard_t Prims.option ->
      FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun x  ->
    fun g  ->
      match g with
      | None |Some
        { FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
          FStar_TypeChecker_Env.deferred = _;
          FStar_TypeChecker_Env.univ_ineqs = _;
          FStar_TypeChecker_Env.implicits = _;_} -> g
      | Some g1 ->
          let f =
            match g1.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.NonTrivial f -> f
            | uu____62 -> failwith "impossible"  in
          let uu____63 =
            let uu___130_64 = g1  in
            let uu____65 =
              let uu____66 =
                let uu____67 =
                  let uu____68 = FStar_Syntax_Syntax.mk_binder x  in
                  [uu____68]  in
                let uu____69 =
                  let uu____76 =
                    let uu____82 =
                      let uu____83 =
                        FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                         in
                      FStar_All.pipe_right uu____83
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    FStar_All.pipe_right uu____82
                      (fun _0_28  -> FStar_Util.Inl _0_28)
                     in
                  Some uu____76  in
                FStar_Syntax_Util.abs uu____67 f uu____69  in
              FStar_All.pipe_left
                (fun _0_29  -> FStar_TypeChecker_Common.NonTrivial _0_29)
                uu____66
               in
            {
              FStar_TypeChecker_Env.guard_f = uu____65;
              FStar_TypeChecker_Env.deferred =
                (uu___130_64.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___130_64.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___130_64.FStar_TypeChecker_Env.implicits)
            }  in
          Some uu____63
  
let apply_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___131_104 = g  in
          let uu____105 =
            let uu____106 =
              let uu____107 =
                let uu____110 =
                  let uu____111 =
                    let uu____121 =
                      let uu____123 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____123]  in
                    (f, uu____121)  in
                  FStar_Syntax_Syntax.Tm_app uu____111  in
                FStar_Syntax_Syntax.mk uu____110  in
              uu____107
                (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_30  -> FStar_TypeChecker_Common.NonTrivial _0_30)
              uu____106
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____105;
            FStar_TypeChecker_Env.deferred =
              (uu___131_104.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___131_104.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___131_104.FStar_TypeChecker_Env.implicits)
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
          let uu___132_145 = g  in
          let uu____146 =
            let uu____147 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____147  in
          {
            FStar_TypeChecker_Env.guard_f = uu____146;
            FStar_TypeChecker_Env.deferred =
              (uu___132_145.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___132_145.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___132_145.FStar_TypeChecker_Env.implicits)
          }
  
let trivial : FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____151 -> failwith "impossible"
  
let conj_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g)
        |(g,FStar_TypeChecker_Common.Trivial ) -> g
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let uu____161 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____161
  
let check_trivial :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_TypeChecker_Common.guard_formula
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____170 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____201 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____201;
          FStar_TypeChecker_Env.deferred =
            (FStar_List.append g1.FStar_TypeChecker_Env.deferred
               g2.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            ((FStar_List.append
                (Prims.fst g1.FStar_TypeChecker_Env.univ_ineqs)
                (Prims.fst g2.FStar_TypeChecker_Env.univ_ineqs)),
              (FStar_List.append
                 (Prims.snd g1.FStar_TypeChecker_Env.univ_ineqs)
                 (Prims.snd g2.FStar_TypeChecker_Env.univ_ineqs)));
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
                       let uu____246 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____246
                       then f1
                       else FStar_Syntax_Util.mk_forall u (Prims.fst b) f1)
                us bs f
               in
            let uu___133_248 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___133_248.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___133_248.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___133_248.FStar_TypeChecker_Env.implicits)
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
               let uu____262 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____262
               then f1
               else
                 (let u =
                    env.FStar_TypeChecker_Env.universe_of env
                      (Prims.fst b).FStar_Syntax_Syntax.sort
                     in
                  FStar_Syntax_Util.mk_forall u (Prims.fst b) f1)) bs f
  
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
            let uu___134_275 = g  in
            let uu____276 =
              let uu____277 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____277  in
            {
              FStar_TypeChecker_Env.guard_f = uu____276;
              FStar_TypeChecker_Env.deferred =
                (uu___134_275.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___134_275.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___134_275.FStar_TypeChecker_Env.implicits)
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
        let uv = FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar  in
        match binders with
        | [] ->
            let uv1 =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k)))
                (Some (k.FStar_Syntax_Syntax.n)) r
               in
            (uv1, uv1)
        | uu____322 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder)
               in
            let k' =
              let uu____337 = FStar_Syntax_Syntax.mk_Total k  in
              FStar_Syntax_Util.arrow binders uu____337  in
            let uv1 =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k')))
                None r
               in
            let uu____357 =
              (FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_app (uv1, args)))
                (Some (k.FStar_Syntax_Syntax.n)) r
               in
            (uu____357, uv1)
  
let mk_eq2 :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____390 = FStar_Syntax_Util.type_u ()  in
        match uu____390 with
        | (t_type,u) ->
            let uu____395 =
              let uu____398 = FStar_TypeChecker_Env.all_binders env  in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____398 t_type  in
            (match uu____395 with
             | (tt,uu____400) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
  
type uvi =
  | TERM of ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) *
  FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let uu___is_TERM : uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____421 -> false
  
let __proj__TERM__item___0 :
  uvi ->
    ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) *
      FStar_Syntax_Syntax.term)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let uu___is_UNIV : uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____447 -> false
  
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
type solution =
  | Success of FStar_TypeChecker_Common.deferred 
  | Failed of (FStar_TypeChecker_Common.prob * Prims.string) 
let uu___is_Success : solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____527 -> false
  
let __proj__Success__item___0 : solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0 
let uu___is_Failed : solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____541 -> false
  
let __proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let uu___is_COVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____558 -> false
  
let uu___is_CONTRAVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____562 -> false
  
let uu___is_INVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____566 -> false
  
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___102_577  ->
    match uu___102_577 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let term_to_string env t =
  let uu____590 =
    let uu____591 = FStar_Syntax_Subst.compress t  in
    uu____591.FStar_Syntax_Syntax.n  in
  match uu____590 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____608 = FStar_Syntax_Print.uvar_to_string u  in
      let uu____612 = FStar_Syntax_Print.term_to_string t1  in
      FStar_Util.format2 "(%s:%s)" uu____608 uu____612
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____615;
         FStar_Syntax_Syntax.pos = uu____616;
         FStar_Syntax_Syntax.vars = uu____617;_},args)
      ->
      let uu____645 = FStar_Syntax_Print.uvar_to_string u  in
      let uu____649 = FStar_Syntax_Print.term_to_string ty  in
      let uu____650 = FStar_Syntax_Print.args_to_string args  in
      FStar_Util.format3 "(%s:%s) %s" uu____645 uu____649 uu____650
  | uu____651 -> FStar_Syntax_Print.term_to_string t 
let prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___103_657  ->
      match uu___103_657 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____661 =
            let uu____663 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____664 =
              let uu____666 =
                term_to_string env p.FStar_TypeChecker_Common.lhs  in
              let uu____667 =
                let uu____669 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs
                   in
                let uu____670 =
                  let uu____672 =
                    let uu____674 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs  in
                    let uu____675 =
                      let uu____677 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs
                         in
                      let uu____678 =
                        let uu____680 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (Prims.fst
                               p.FStar_TypeChecker_Common.logical_guard)
                           in
                        let uu____681 =
                          let uu____683 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t")
                             in
                          [uu____683]  in
                        uu____680 :: uu____681  in
                      uu____677 :: uu____678  in
                    uu____674 :: uu____675  in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____672
                   in
                uu____669 :: uu____670  in
              uu____666 :: uu____667  in
            uu____663 :: uu____664  in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____661
      | FStar_TypeChecker_Common.CProb p ->
          let uu____688 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____689 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____688
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____689
  
let uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___104_695  ->
      match uu___104_695 with
      | UNIV (u,t) ->
          let x =
            let uu____699 = FStar_Options.hide_uvar_nums ()  in
            if uu____699
            then "?"
            else
              (let uu____701 = FStar_Unionfind.uvar_id u  in
               FStar_All.pipe_right uu____701 FStar_Util.string_of_int)
             in
          let uu____703 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____703
      | TERM ((u,uu____705),t) ->
          let x =
            let uu____710 = FStar_Options.hide_uvar_nums ()  in
            if uu____710
            then "?"
            else
              (let uu____712 = FStar_Unionfind.uvar_id u  in
               FStar_All.pipe_right uu____712 FStar_Util.string_of_int)
             in
          let uu____716 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____716
  
let uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____725 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____725 (FStar_String.concat ", ")
  
let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____733 =
      let uu____735 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____735
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____733 (FStar_String.concat ", ")
  
let args_to_string args =
  let uu____753 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____761  ->
            match uu____761 with
            | (x,uu____765) -> FStar_Syntax_Print.term_to_string x))
     in
  FStar_All.pipe_right uu____753 (FStar_String.concat " ") 
let empty_worklist : FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____770 =
      let uu____771 = FStar_Options.eager_inference ()  in
      Prims.op_Negation uu____771  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____770;
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
        let uu___135_784 = empty_worklist env  in
        {
          attempting = [prob];
          wl_deferred = (uu___135_784.wl_deferred);
          ctr = (uu___135_784.ctr);
          defer_ok = (uu___135_784.defer_ok);
          smt_ok;
          tcenv = (uu___135_784.tcenv)
        }
  
let singleton :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true 
let wl_of_guard env g =
  let uu___136_809 = empty_worklist env  in
  let uu____810 = FStar_List.map Prims.snd g  in
  {
    attempting = uu____810;
    wl_deferred = (uu___136_809.wl_deferred);
    ctr = (uu___136_809.ctr);
    defer_ok = false;
    smt_ok = (uu___136_809.smt_ok);
    tcenv = (uu___136_809.tcenv)
  } 
let defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___137_822 = wl  in
        {
          attempting = (uu___137_822.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___137_822.ctr);
          defer_ok = (uu___137_822.defer_ok);
          smt_ok = (uu___137_822.smt_ok);
          tcenv = (uu___137_822.tcenv)
        }
  
let attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist =
  fun probs  ->
    fun wl  ->
      let uu___138_834 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___138_834.wl_deferred);
        ctr = (uu___138_834.ctr);
        defer_ok = (uu___138_834.defer_ok);
        smt_ok = (uu___138_834.smt_ok);
        tcenv = (uu___138_834.tcenv)
      }
  
let giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____845 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____845
         then
           let uu____846 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____846
         else ());
        Failed (prob, reason)
  
let invert_rel : FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___105_850  ->
    match uu___105_850 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert p =
  let uu___139_866 = p  in
  {
    FStar_TypeChecker_Common.pid =
      (uu___139_866.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___139_866.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___139_866.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___139_866.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___139_866.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___139_866.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___139_866.FStar_TypeChecker_Common.rank)
  } 
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p 
let maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___106_887  ->
    match uu___106_887 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_31  -> FStar_TypeChecker_Common.TProb _0_31)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_32  -> FStar_TypeChecker_Common.CProb _0_32)
  
let vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___107_903  ->
      match uu___107_903 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let p_pid : FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___108_906  ->
    match uu___108_906 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___109_915  ->
    match uu___109_915 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___110_925  ->
    match uu___110_925 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___111_935  ->
    match uu___111_935 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let p_guard :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun uu___112_946  ->
    match uu___112_946 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let p_scope : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___113_957  ->
    match uu___113_957 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
  
let p_invert : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___114_966  ->
    match uu___114_966 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_33  -> FStar_TypeChecker_Common.TProb _0_33) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_34  -> FStar_TypeChecker_Common.CProb _0_34) (invert p)
  
let is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____980 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____980 = (Prims.parse_int "1")
  
let next_pid : Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____991  -> FStar_Util.incr ctr; FStar_ST.read ctr 
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1041 = next_pid ()  in
  let uu____1042 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0  in
  {
    FStar_TypeChecker_Common.pid = uu____1041;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1042;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  } 
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env  in
  let uu____1089 = next_pid ()  in
  let uu____1090 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0  in
  {
    FStar_TypeChecker_Common.pid = uu____1089;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1090;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  } 
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1131 = next_pid ()  in
  {
    FStar_TypeChecker_Common.pid = uu____1131;
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
        let uu____1183 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel")
           in
        if uu____1183
        then
          let uu____1184 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____1185 = prob_to_string env d  in
          let uu____1186 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1184 uu____1185 uu____1186 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1191 -> failwith "impossible"  in
           let uu____1192 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1200 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____1201 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____1200, uu____1201)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1205 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____1206 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____1205, uu____1206)
              in
           match uu____1192 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let commit : uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___115_1215  ->
            match uu___115_1215 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Unionfind.union u u'
                 | uu____1222 -> FStar_Unionfind.change u (Some t))
            | TERM ((u,uu____1225),t) -> FStar_Syntax_Util.set_uvar u t))
  
let find_term_uvar :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
    FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term Prims.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___116_1248  ->
           match uu___116_1248 with
           | UNIV uu____1250 -> None
           | TERM ((u,uu____1254),t) ->
               let uu____1258 = FStar_Unionfind.equivalent uv u  in
               if uu____1258 then Some t else None)
  
let find_univ_uvar :
  FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe Prims.option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___117_1277  ->
           match uu___117_1277 with
           | UNIV (u',t) ->
               let uu____1281 = FStar_Unionfind.equivalent u u'  in
               if uu____1281 then Some t else None
           | uu____1285 -> None)
  
let whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1292 =
        let uu____1293 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1293
         in
      FStar_Syntax_Subst.compress uu____1292
  
let sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1300 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____1300
  
let norm_arg env t =
  let uu____1319 = sn env (Prims.fst t)  in (uu____1319, (Prims.snd t)) 
let sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1336  ->
              match uu____1336 with
              | (x,imp) ->
                  let uu____1343 =
                    let uu___140_1344 = x  in
                    let uu____1345 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___140_1344.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___140_1344.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1345
                    }  in
                  (uu____1343, imp)))
  
let norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1360 = aux u3  in FStar_Syntax_Syntax.U_succ uu____1360
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1363 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____1363
        | uu____1365 -> u2  in
      let uu____1366 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1366
  
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0 
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1473 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           match uu____1473 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1485;
               FStar_Syntax_Syntax.pos = uu____1486;
               FStar_Syntax_Syntax.vars = uu____1487;_} ->
               ((x1.FStar_Syntax_Syntax.sort), (Some (x1, phi1)))
           | tt ->
               let uu____1508 =
                 let uu____1509 = FStar_Syntax_Print.term_to_string tt  in
                 let uu____1510 = FStar_Syntax_Print.tag_of_term tt  in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1509
                   uu____1510
                  in
               failwith uu____1508)
    | FStar_Syntax_Syntax.Tm_uinst _
      |FStar_Syntax_Syntax.Tm_fvar _|FStar_Syntax_Syntax.Tm_app _ ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           let uu____1545 =
             let uu____1546 = FStar_Syntax_Subst.compress t1'  in
             uu____1546.FStar_Syntax_Syntax.n  in
           match uu____1545 with
           | FStar_Syntax_Syntax.Tm_refine uu____1558 -> aux true t1'
           | uu____1563 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_type _
      |FStar_Syntax_Syntax.Tm_constant _
       |FStar_Syntax_Syntax.Tm_name _
        |FStar_Syntax_Syntax.Tm_bvar _
         |FStar_Syntax_Syntax.Tm_arrow _
          |FStar_Syntax_Syntax.Tm_abs _
           |FStar_Syntax_Syntax.Tm_uvar _
            |FStar_Syntax_Syntax.Tm_let _|FStar_Syntax_Syntax.Tm_match _
        -> (t11, None)
    | FStar_Syntax_Syntax.Tm_meta _
      |FStar_Syntax_Syntax.Tm_ascribed _
       |FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____1598 =
          let uu____1599 = FStar_Syntax_Print.term_to_string t11  in
          let uu____1600 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1599
            uu____1600
           in
        failwith uu____1598
     in
  let uu____1610 = whnf env t1  in aux false uu____1610 
let unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1619 =
        let uu____1629 = empty_worklist env  in
        base_and_refinement env uu____1629 t  in
      FStar_All.pipe_right uu____1619 Prims.fst
  
let trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____1653 = FStar_Syntax_Syntax.null_bv t  in
    (uu____1653, FStar_Syntax_Util.t_true)
  
let as_refinement env wl t =
  let uu____1673 = base_and_refinement env wl t  in
  match uu____1673 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
  
let force_refinement uu____1732 =
  match uu____1732 with
  | (t_base,refopt) ->
      let uu____1746 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base  in
      (match uu____1746 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
  
let wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___118_1770  ->
      match uu___118_1770 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1774 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1775 =
            let uu____1776 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
            FStar_Syntax_Print.term_to_string uu____1776  in
          let uu____1777 =
            let uu____1778 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
            FStar_Syntax_Print.term_to_string uu____1778  in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____1774 uu____1775
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1777
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1782 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1783 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____1784 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____1782 uu____1783
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1784
  
let wl_to_string : worklist -> Prims.string =
  fun wl  ->
    let uu____1788 =
      let uu____1790 =
        let uu____1792 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____1802  ->
                  match uu____1802 with | (uu____1806,uu____1807,x) -> x))
           in
        FStar_List.append wl.attempting uu____1792  in
      FStar_List.map (wl_prob_to_string wl) uu____1790  in
    FStar_All.pipe_right uu____1788 (FStar_String.concat "\n\t")
  
let u_abs :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____1825 =
          let uu____1835 =
            let uu____1836 = FStar_Syntax_Subst.compress k  in
            uu____1836.FStar_Syntax_Syntax.n  in
          match uu____1835 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____1877 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____1877)
              else
                (let uu____1891 = FStar_Syntax_Util.abs_formals t  in
                 match uu____1891 with
                 | (ys',t1,uu____1912) ->
                     let uu____1925 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____1925))
          | uu____1946 ->
              let uu____1947 =
                let uu____1953 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____1953)  in
              ((ys, t), uu____1947)
           in
        match uu____1825 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____2008 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____2008 c  in
               let uu____2010 =
                 let uu____2017 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_35  -> FStar_Util.Inl _0_35)
                    in
                 FStar_All.pipe_right uu____2017 (fun _0_36  -> Some _0_36)
                  in
               FStar_Syntax_Util.abs ys1 t1 uu____2010)
  
let solve_prob' :
  Prims.bool ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term Prims.option ->
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
            let uu____2068 = p_guard prob  in
            match uu____2068 with
            | (uu____2071,uv) ->
                ((let uu____2074 =
                    let uu____2075 = FStar_Syntax_Subst.compress uv  in
                    uu____2075.FStar_Syntax_Syntax.n  in
                  match uu____2074 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob  in
                      let phi1 = u_abs k bs phi  in
                      ((let uu____2095 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel")
                           in
                        if uu____2095
                        then
                          let uu____2096 =
                            FStar_Util.string_of_int (p_pid prob)  in
                          let uu____2097 =
                            FStar_Syntax_Print.term_to_string uv  in
                          let uu____2098 =
                            FStar_Syntax_Print.term_to_string phi1  in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2096
                            uu____2097 uu____2098
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2102 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___141_2105 = wl  in
                  {
                    attempting = (uu___141_2105.attempting);
                    wl_deferred = (uu___141_2105.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___141_2105.defer_ok);
                    smt_ok = (uu___141_2105.smt_ok);
                    tcenv = (uu___141_2105.tcenv)
                  }))
  
let extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2118 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck")
            in
         if uu____2118
         then
           let uu____2119 = FStar_Util.string_of_int pid  in
           let uu____2120 =
             let uu____2121 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____2121 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2119 uu____2120
         else ());
        commit sol;
        (let uu___142_2126 = wl  in
         {
           attempting = (uu___142_2126.attempting);
           wl_deferred = (uu___142_2126.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___142_2126.defer_ok);
           smt_ok = (uu___142_2126.smt_ok);
           tcenv = (uu___142_2126.tcenv)
         })
  
let solve_prob :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term Prims.option ->
      uvi Prims.list -> worklist -> worklist
  =
  fun prob  ->
    fun logical_guard  ->
      fun uvis  ->
        fun wl  ->
          let conj_guard1 t g =
            match (t, g) with
            | (uu____2155,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2163 = FStar_Syntax_Util.mk_conj t1 f  in
                Some uu____2163
             in
          (let uu____2169 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck")
              in
           if uu____2169
           then
             let uu____2170 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____2171 =
               let uu____2172 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____2172 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2170 uu____2171
           else ());
          solve_prob' false prob logical_guard uvis wl
  
let rec occurs wl uk t =
  let uu____2197 =
    let uu____2201 = FStar_Syntax_Free.uvars t  in
    FStar_All.pipe_right uu____2201 FStar_Util.set_elements  in
  FStar_All.pipe_right uu____2197
    (FStar_Util.for_some
       (fun uu____2222  ->
          match uu____2222 with
          | (uv,uu____2230) -> FStar_Unionfind.equivalent uv (Prims.fst uk)))
  
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2274 = occurs wl uk t  in Prims.op_Negation uu____2274  in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2279 =
         let uu____2280 = FStar_Syntax_Print.uvar_to_string (Prims.fst uk)
            in
         let uu____2284 = FStar_Syntax_Print.term_to_string t  in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2280 uu____2284
          in
       Some uu____2279)
     in
  (occurs_ok, msg) 
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t  in
  let uu____2332 = occurs_check env wl uk t  in
  match uu____2332 with
  | (occurs_ok,msg) ->
      let uu____2349 = FStar_Util.set_is_subset_of fvs_t fvs  in
      (occurs_ok, uu____2349, (msg, fvs, fvs_t))
  
let intersect_vars v1 v2 =
  let as_set v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (Prims.fst x) out)
         FStar_Syntax_Syntax.no_names)
     in
  let v1_set = as_set v1  in
  let uu____2413 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2437  ->
            fun uu____2438  ->
              match (uu____2437, uu____2438) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2481 =
                    let uu____2482 = FStar_Util.set_mem x v1_set  in
                    FStar_All.pipe_left Prims.op_Negation uu____2482  in
                  if uu____2481
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort  in
                     let uu____2496 =
                       FStar_Util.set_is_subset_of fvs isect_set  in
                     if uu____2496
                     then
                       let uu____2503 = FStar_Util.set_add x isect_set  in
                       (((x, imp) :: isect), uu____2503)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names))
     in
  match uu____2413 with | (isect,uu____2525) -> FStar_List.rev isect 
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2574  ->
          fun uu____2575  ->
            match (uu____2574, uu____2575) with
            | ((a,uu____2585),(b,uu____2587)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg  in
  match (Prims.fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2631 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2637  ->
                match uu____2637 with
                | (b,uu____2641) -> FStar_Syntax_Syntax.bv_eq a b))
         in
      if uu____2631 then None else Some (a, (Prims.snd hd1))
  | uu____2650 -> None 
let rec pat_vars :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list ->
        FStar_Syntax_Syntax.binders Prims.option
  =
  fun env  ->
    fun seen  ->
      fun args  ->
        match args with
        | [] -> Some (FStar_List.rev seen)
        | hd1::rest ->
            let uu____2693 = pat_var_opt env seen hd1  in
            (match uu____2693 with
             | None  ->
                 ((let uu____2701 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel")
                      in
                   if uu____2701
                   then
                     let uu____2702 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (Prims.fst hd1)
                        in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____2702
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
  
let is_flex : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2714 =
      let uu____2715 = FStar_Syntax_Subst.compress t  in
      uu____2715.FStar_Syntax_Syntax.n  in
    match uu____2714 with
    | FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
         FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
         FStar_Syntax_Syntax.vars = _;_},_)
        -> true
    | uu____2731 -> false
  
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____2793;
         FStar_Syntax_Syntax.pos = uu____2794;
         FStar_Syntax_Syntax.vars = uu____2795;_},args)
      -> (t, uv, k, args)
  | uu____2836 -> failwith "Not a flex-uvar" 
let destruct_flex_pattern env t =
  let uu____2890 = destruct_flex_t t  in
  match uu____2890 with
  | (t1,uv,k,args) ->
      let uu____2958 = pat_vars env [] args  in
      (match uu____2958 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3014 -> ((t1, uv, k, args), None))
  
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth Prims.option *
  FStar_Syntax_Syntax.delta_depth Prims.option) 
  | HeadMatch 
  | FullMatch 
let uu___is_MisMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3062 -> false
  
let __proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth Prims.option *
      FStar_Syntax_Syntax.delta_depth Prims.option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let uu___is_HeadMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3085 -> false
  
let uu___is_FullMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3089 -> false
  
let head_match : match_result -> match_result =
  fun uu___119_3092  ->
    match uu___119_3092 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3101 -> HeadMatch
  
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3114 ->
          let uu____3115 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____3115 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3125 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
  
let rec delta_depth_of_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth Prims.option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta _|FStar_Syntax_Syntax.Tm_delayed _ ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown 
        |FStar_Syntax_Syntax.Tm_bvar _
         |FStar_Syntax_Syntax.Tm_name _
          |FStar_Syntax_Syntax.Tm_uvar _
           |FStar_Syntax_Syntax.Tm_let _|FStar_Syntax_Syntax.Tm_match _
          -> None
      | FStar_Syntax_Syntax.Tm_uinst (t2,_)
        |FStar_Syntax_Syntax.Tm_ascribed (t2,_,_)
         |FStar_Syntax_Syntax.Tm_app (t2,_)|FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
             FStar_Syntax_Syntax.sort = t2;_},_)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant _
        |FStar_Syntax_Syntax.Tm_type _
         |FStar_Syntax_Syntax.Tm_arrow _|FStar_Syntax_Syntax.Tm_abs _ ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3193 = fv_delta_depth env fv  in Some uu____3193
  
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
            let uu____3212 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____3212
            then FullMatch
            else
              (let uu____3214 =
                 let uu____3219 =
                   let uu____3221 = fv_delta_depth env f  in Some uu____3221
                    in
                 let uu____3222 =
                   let uu____3224 = fv_delta_depth env g  in Some uu____3224
                    in
                 (uu____3219, uu____3222)  in
               MisMatch uu____3214)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3228),FStar_Syntax_Syntax.Tm_uinst (g,uu____3230)) ->
            let uu____3239 = head_matches env f g  in
            FStar_All.pipe_right uu____3239 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3246),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3248)) ->
            let uu____3273 = FStar_Unionfind.equivalent uv uv'  in
            if uu____3273 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3281),FStar_Syntax_Syntax.Tm_refine (y,uu____3283)) ->
            let uu____3292 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____3292 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3294),uu____3295) ->
            let uu____3300 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____3300 head_match
        | (uu____3301,FStar_Syntax_Syntax.Tm_refine (x,uu____3303)) ->
            let uu____3308 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____3308 head_match
        | (FStar_Syntax_Syntax.Tm_type _,FStar_Syntax_Syntax.Tm_type _)
          |(FStar_Syntax_Syntax.Tm_arrow _,FStar_Syntax_Syntax.Tm_arrow _) ->
            HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3314),FStar_Syntax_Syntax.Tm_app (head',uu____3316))
            ->
            let uu____3345 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____3345 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3347),uu____3348) ->
            let uu____3363 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____3363 head_match
        | (uu____3364,FStar_Syntax_Syntax.Tm_app (head1,uu____3366)) ->
            let uu____3381 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____3381 head_match
        | uu____3382 ->
            let uu____3385 =
              let uu____3390 = delta_depth_of_term env t11  in
              let uu____3392 = delta_depth_of_term env t21  in
              (uu____3390, uu____3392)  in
            MisMatch uu____3385
  
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3428 = FStar_Syntax_Util.head_and_args t  in
    match uu____3428 with
    | (head1,uu____3440) ->
        let uu____3455 =
          let uu____3456 = FStar_Syntax_Util.un_uinst head1  in
          uu____3456.FStar_Syntax_Syntax.n  in
        (match uu____3455 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3461 =
               let uu____3462 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               FStar_All.pipe_right uu____3462 FStar_Option.isSome  in
             if uu____3461
             then
               let uu____3476 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t
                  in
               FStar_All.pipe_right uu____3476 (fun _0_37  -> Some _0_37)
             else None
         | uu____3479 -> None)
     in
  let success d r t11 t21 =
    (r, (if d > (Prims.parse_int "0") then Some (t11, t21) else None))  in
  let fail r = (r, None)  in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21  in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),_)|MisMatch
      (_,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____3559 =
             let uu____3564 = maybe_inline t11  in
             let uu____3566 = maybe_inline t21  in (uu____3564, uu____3566)
              in
           match uu____3559 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____3591 = FStar_TypeChecker_Common.decr_delta_depth d1  in
        (match uu____3591 with
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
        let uu____3606 =
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
             let uu____3614 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21
                in
             (t11, uu____3614))
           in
        (match uu____3606 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____3622 -> fail r
    | uu____3627 -> success n_delta r t11 t21  in
  aux true (Prims.parse_int "0") t1 t2 
type tc =
  | T of (FStar_Syntax_Syntax.term *
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  
  | C of FStar_Syntax_Syntax.comp 
let uu___is_T : tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____3652 -> false 
let __proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term *
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0 
let uu___is_C : tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____3682 -> false 
let __proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list
let generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____3697 = FStar_Syntax_Util.type_u ()  in
      match uu____3697 with
      | (t,uu____3701) ->
          let uu____3702 = new_uvar r binders t  in Prims.fst uu____3702
  
let kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____3711 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____3711 Prims.fst
  
let rec decompose :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      ((tc Prims.list -> FStar_Syntax_Syntax.term) *
        (FStar_Syntax_Syntax.term -> Prims.bool) *
        (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list)
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let matches t' =
        let uu____3753 = head_matches env t1 t'  in
        match uu____3753 with
        | MisMatch uu____3754 -> false
        | uu____3759 -> true  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____3819,imp),T (t2,uu____3822)) -> (t2, imp)
                     | uu____3839 -> failwith "Bad reconstruction") args
                args'
               in
            (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1)))
              None t1.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____3883  ->
                    match uu____3883 with
                    | (t2,uu____3891) ->
                        (None, INVARIANT, (T (t2, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let fail uu____3924 = failwith "Bad reconstruction"  in
          let uu____3925 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____3925 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____3978))::tcs2) ->
                       aux
                         (((let uu___143_4000 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___143_4000.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___143_4000.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4010 -> failwith "Bad reconstruction"  in
                 aux [] bs1 tcs  in
               let rec decompose1 out uu___120_4041 =
                 match uu___120_4041 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((Prims.fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest
                  in
               let uu____4104 = decompose1 [] bs1  in
               (rebuild, matches, uu____4104))
      | uu____4132 ->
          let rebuild uu___121_4137 =
            match uu___121_4137 with
            | [] -> t1
            | uu____4139 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t2  -> true)), [])
  
let un_T : tc -> FStar_Syntax_Syntax.term =
  fun uu___122_4158  ->
    match uu___122_4158 with
    | T (t,uu____4160) -> t
    | uu____4169 -> failwith "Impossible"
  
let arg_of_tc : tc -> FStar_Syntax_Syntax.arg =
  fun uu___123_4172  ->
    match uu___123_4172 with
    | T (t,uu____4174) -> FStar_Syntax_Syntax.as_arg t
    | uu____4183 -> failwith "Impossible"
  
let imitation_sub_probs :
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.args ->
          (FStar_Syntax_Syntax.binder Prims.option * variance * tc)
            Prims.list ->
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
              | (uu____4252,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r  in
                  let uu____4271 = new_uvar r scope1 k  in
                  (match uu____4271 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4283 ->
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_app (gi, args))) None
                               r
                          in
                       let uu____4302 =
                         let uu____4303 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm"
                            in
                         FStar_All.pipe_left
                           (fun _0_38  ->
                              FStar_TypeChecker_Common.TProb _0_38)
                           uu____4303
                          in
                       ((T (gi_xs, mk_kind)), uu____4302))
              | (uu____4312,uu____4313,C uu____4314) -> failwith "impos"  in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4401 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4412;
                         FStar_Syntax_Syntax.pos = uu____4413;
                         FStar_Syntax_Syntax.vars = uu____4414;_})
                        ->
                        let uu____4429 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____4429 with
                         | (T (gi_xs,uu____4445),prob) ->
                             let uu____4455 =
                               let uu____4456 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                               FStar_All.pipe_left (fun _0_39  -> C _0_39)
                                 uu____4456
                                in
                             (uu____4455, [prob])
                         | uu____4458 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4468;
                         FStar_Syntax_Syntax.pos = uu____4469;
                         FStar_Syntax_Syntax.vars = uu____4470;_})
                        ->
                        let uu____4485 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____4485 with
                         | (T (gi_xs,uu____4501),prob) ->
                             let uu____4511 =
                               let uu____4512 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                                  in
                               FStar_All.pipe_left (fun _0_40  -> C _0_40)
                                 uu____4512
                                in
                             (uu____4511, [prob])
                         | uu____4514 -> failwith "impossible")
                    | (uu____4520,uu____4521,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____4523;
                         FStar_Syntax_Syntax.pos = uu____4524;
                         FStar_Syntax_Syntax.vars = uu____4525;_})
                        ->
                        let components =
                          FStar_All.pipe_right
                            c.FStar_Syntax_Syntax.effect_args
                            (FStar_List.map
                               (fun t  ->
                                  (None, INVARIANT,
                                    (T ((Prims.fst t), generic_kind)))))
                           in
                        let components1 =
                          (None, COVARIANT,
                            (T
                               ((c.FStar_Syntax_Syntax.result_typ),
                                 kind_type)))
                          :: components  in
                        let uu____4599 =
                          let uu____4604 =
                            FStar_List.map (sub_prob scope1 args) components1
                             in
                          FStar_All.pipe_right uu____4604 FStar_List.unzip
                           in
                        (match uu____4599 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____4633 =
                                 let uu____4634 =
                                   let uu____4637 = FStar_List.hd tcs  in
                                   FStar_All.pipe_right uu____4637 un_T  in
                                 let uu____4638 =
                                   let uu____4644 = FStar_List.tl tcs  in
                                   FStar_All.pipe_right uu____4644
                                     (FStar_List.map arg_of_tc)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____4634;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____4638;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 }  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____4633
                                in
                             ((C gi_xs), sub_probs))
                    | uu____4649 ->
                        let uu____4656 = sub_prob scope1 args q  in
                        (match uu____4656 with
                         | (ktec,prob) -> (ktec, [prob]))
                     in
                  (match uu____4401 with
                   | (tc,probs) ->
                       let uu____4674 =
                         match q with
                         | (Some b,uu____4700,uu____4701) ->
                             let uu____4709 =
                               let uu____4713 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b
                                  in
                               uu____4713 :: args  in
                             ((Some b), (b :: scope1), uu____4709)
                         | uu____4731 -> (None, scope1, args)  in
                       (match uu____4674 with
                        | (bopt,scope2,args1) ->
                            let uu____4774 = aux scope2 args1 qs2  in
                            (match uu____4774 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____4795 =
                                         let uu____4797 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob) Prims.fst))
                                            in
                                         f :: uu____4797  in
                                       FStar_Syntax_Util.mk_conj_l uu____4795
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (Prims.fst b).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____4810 =
                                         let uu____4812 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (Prims.fst b) f
                                            in
                                         let uu____4813 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob) Prims.fst))
                                            in
                                         uu____4812 :: uu____4813  in
                                       FStar_Syntax_Util.mk_conj_l uu____4810
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
    Prims.option * variance * tc) Prims.list))
let rigid_rigid : Prims.int = (Prims.parse_int "0") 
let flex_rigid_eq : Prims.int = (Prims.parse_int "1") 
let flex_refine_inner : Prims.int = (Prims.parse_int "2") 
let flex_refine : Prims.int = (Prims.parse_int "3") 
let flex_rigid : Prims.int = (Prims.parse_int "4") 
let rigid_flex : Prims.int = (Prims.parse_int "5") 
let refine_flex : Prims.int = (Prims.parse_int "6") 
let flex_flex : Prims.int = (Prims.parse_int "7") 
let compress_tprob wl p =
  let uu___144_4866 = p  in
  let uu____4869 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
  let uu____4870 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
  {
    FStar_TypeChecker_Common.pid =
      (uu___144_4866.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____4869;
    FStar_TypeChecker_Common.relation =
      (uu___144_4866.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____4870;
    FStar_TypeChecker_Common.element =
      (uu___144_4866.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___144_4866.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___144_4866.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___144_4866.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___144_4866.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___144_4866.FStar_TypeChecker_Common.rank)
  } 
let compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____4880 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____4880
            (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
      | FStar_TypeChecker_Common.CProb uu____4885 -> p
  
let rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int * FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____4899 = compress_prob wl pr  in
        FStar_All.pipe_right uu____4899 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____4905 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____4905 with
           | (lh,uu____4918) ->
               let uu____4933 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____4933 with
                | (rh,uu____4946) ->
                    let uu____4961 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____4970,FStar_Syntax_Syntax.Tm_uvar uu____4971)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar _,_)
                        |(_,FStar_Syntax_Syntax.Tm_uvar _) when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____4996,uu____4997)
                          ->
                          let uu____5006 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____5006 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5046 ->
                                    let rank =
                                      let uu____5053 = is_top_level_prob prob
                                         in
                                      if uu____5053
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____5055 =
                                      let uu___145_5058 = tp  in
                                      let uu____5061 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___145_5058.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___145_5058.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___145_5058.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5061;
                                        FStar_TypeChecker_Common.element =
                                          (uu___145_5058.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___145_5058.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___145_5058.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___145_5058.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___145_5058.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___145_5058.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____5055)))
                      | (uu____5071,FStar_Syntax_Syntax.Tm_uvar uu____5072)
                          ->
                          let uu____5081 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____5081 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5121 ->
                                    let uu____5127 =
                                      let uu___146_5132 = tp  in
                                      let uu____5135 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___146_5132.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5135;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___146_5132.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___146_5132.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___146_5132.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___146_5132.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___146_5132.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___146_5132.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___146_5132.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___146_5132.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____5127)))
                      | (uu____5151,uu____5152) -> (rigid_rigid, tp)  in
                    (match uu____4961 with
                     | (rank,tp1) ->
                         let uu____5163 =
                           FStar_All.pipe_right
                             (let uu___147_5166 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___147_5166.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___147_5166.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___147_5166.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___147_5166.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___147_5166.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___147_5166.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___147_5166.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___147_5166.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___147_5166.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_42  ->
                                FStar_TypeChecker_Common.TProb _0_42)
                            in
                         (rank, uu____5163))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5172 =
            FStar_All.pipe_right
              (let uu___148_5175 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___148_5175.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___148_5175.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___148_5175.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___148_5175.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___148_5175.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___148_5175.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___148_5175.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___148_5175.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___148_5175.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_43  -> FStar_TypeChecker_Common.CProb _0_43)
             in
          (rigid_rigid, uu____5172)
  
let next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob Prims.option *
      FStar_TypeChecker_Common.prob Prims.list * Prims.int)
  =
  fun wl  ->
    let rec aux uu____5207 probs =
      match uu____5207 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5237 = rank wl hd1  in
               (match uu____5237 with
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
    match projectee with | UDeferred _0 -> true | uu____5302 -> false
  
let __proj__UDeferred__item___0 : univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let uu___is_USolved : univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5314 -> false
  
let __proj__USolved__item___0 : univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let uu___is_UFailed : univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5326 -> false
  
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
                        let uu____5363 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____5363 with
                        | (k,uu____5367) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Unionfind.equivalent v1 v2
                             | uu____5372 -> false)))
            | uu____5373 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
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
                        let uu____5416 =
                          really_solve_universe_eq pid_orig wl1 u13 u23  in
                        (match uu____5416 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5419 -> USolved wl1  in
                  aux wl us1 us2
                else
                  (let uu____5425 =
                     let uu____5426 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____5427 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5426
                       uu____5427
                      in
                   UFailed uu____5425)
            | (FStar_Syntax_Syntax.U_max us,u')
              |(u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5444 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____5444 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____5447 ->
                let uu____5450 =
                  let uu____5451 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____5452 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____5451
                    uu____5452 msg
                   in
                UFailed uu____5450
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar _,_)
            |(FStar_Syntax_Syntax.U_unknown ,_)
             |(_,FStar_Syntax_Syntax.U_bvar _)
              |(_,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____5459 =
                let uu____5460 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____5461 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5460 uu____5461
                 in
              failwith uu____5459
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____5473 = FStar_Unionfind.equivalent v1 v2  in
              if uu____5473
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u)
            |(u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____5486 = occurs_univ v1 u3  in
              if uu____5486
              then
                let uu____5487 =
                  let uu____5488 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____5489 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____5488 uu____5489
                   in
                try_umax_components u11 u21 uu____5487
              else
                (let uu____5491 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____5491)
          | (FStar_Syntax_Syntax.U_max _,_)|(_,FStar_Syntax_Syntax.U_max _)
              ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____5501 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____5501
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ _,FStar_Syntax_Syntax.U_zero )
            |(FStar_Syntax_Syntax.U_succ _,FStar_Syntax_Syntax.U_name _)
             |(FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ _)
              |(FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name _)
               |(FStar_Syntax_Syntax.U_name _,FStar_Syntax_Syntax.U_succ _)
                |(FStar_Syntax_Syntax.U_name _,FStar_Syntax_Syntax.U_zero )
              -> UFailed "Incompatible universes"
  
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
  let uu____5572 = bc1  in
  match uu____5572 with
  | (bs1,mk_cod1) ->
      let uu____5597 = bc2  in
      (match uu____5597 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____5644 = FStar_Util.first_N n1 bs  in
             match uu____5644 with
             | (bs3,rest) ->
                 let uu____5658 = mk_cod rest  in (bs3, uu____5658)
              in
           let l1 = FStar_List.length bs1  in
           let l2 = FStar_List.length bs2  in
           if l1 = l2
           then
             let uu____5676 =
               let uu____5680 = mk_cod1 []  in (bs1, uu____5680)  in
             let uu____5682 =
               let uu____5686 = mk_cod2 []  in (bs2, uu____5686)  in
             (uu____5676, uu____5682)
           else
             if l1 > l2
             then
               (let uu____5708 = curry l2 bs1 mk_cod1  in
                let uu____5715 =
                  let uu____5719 = mk_cod2 []  in (bs2, uu____5719)  in
                (uu____5708, uu____5715))
             else
               (let uu____5728 =
                  let uu____5732 = mk_cod1 []  in (bs1, uu____5732)  in
                let uu____5734 = curry l1 bs2 mk_cod2  in
                (uu____5728, uu____5734)))
  
let rec solve : FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____5838 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____5838
       then
         let uu____5839 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____5839
       else ());
      (let uu____5841 = next_prob probs  in
       match uu____5841 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___149_5854 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___149_5854.wl_deferred);
               ctr = (uu___149_5854.ctr);
               defer_ok = (uu___149_5854.defer_ok);
               smt_ok = (uu___149_5854.smt_ok);
               tcenv = (uu___149_5854.tcenv)
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
                  let uu____5861 = solve_flex_rigid_join env tp probs1  in
                  (match uu____5861 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____5865 = solve_rigid_flex_meet env tp probs1  in
                     match uu____5865 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____5869,uu____5870) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____5879 ->
                let uu____5884 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____5912  ->
                          match uu____5912 with
                          | (c,uu____5917,uu____5918) -> c < probs.ctr))
                   in
                (match uu____5884 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____5940 =
                            FStar_List.map
                              (fun uu____5946  ->
                                 match uu____5946 with
                                 | (uu____5952,x,y) -> (x, y))
                              probs.wl_deferred
                             in
                          Success uu____5940
                      | uu____5955 ->
                          let uu____5960 =
                            let uu___150_5961 = probs  in
                            let uu____5962 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____5971  ->
                                      match uu____5971 with
                                      | (uu____5975,uu____5976,y) -> y))
                               in
                            {
                              attempting = uu____5962;
                              wl_deferred = rest;
                              ctr = (uu___150_5961.ctr);
                              defer_ok = (uu___150_5961.defer_ok);
                              smt_ok = (uu___150_5961.smt_ok);
                              tcenv = (uu___150_5961.tcenv)
                            }  in
                          solve env uu____5960))))

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
            let uu____5983 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____5983 with
            | USolved wl1 ->
                let uu____5985 = solve_prob orig None [] wl1  in
                solve env uu____5985
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
                  let uu____6019 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____6019 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6022 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6030;
                  FStar_Syntax_Syntax.pos = uu____6031;
                  FStar_Syntax_Syntax.vars = uu____6032;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6035;
                  FStar_Syntax_Syntax.pos = uu____6036;
                  FStar_Syntax_Syntax.vars = uu____6037;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst _,_)
              |(_,FStar_Syntax_Syntax.Tm_uinst _) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6053 -> USolved wl

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
            ((let uu____6061 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____6061
              then
                let uu____6062 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6062 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

and solve_rigid_flex_meet :
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist Prims.option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6070 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____6070
         then
           let uu____6071 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6071
         else ());
        (let uu____6073 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____6073 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6115 = head_matches_delta env () t1 t2  in
               match uu____6115 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6137 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____6163 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____6172 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____6173 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____6172, uu____6173)
                          | None  ->
                              let uu____6176 = FStar_Syntax_Subst.compress t1
                                 in
                              let uu____6177 = FStar_Syntax_Subst.compress t2
                                 in
                              (uu____6176, uu____6177)
                           in
                        (match uu____6163 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6199 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_44  ->
                                    FStar_TypeChecker_Common.TProb _0_44)
                                 uu____6199
                                in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6222 =
                                    let uu____6228 =
                                      let uu____6231 =
                                        let uu____6234 =
                                          let uu____6235 =
                                            let uu____6240 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2
                                               in
                                            (x, uu____6240)  in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6235
                                           in
                                        FStar_Syntax_Syntax.mk uu____6234  in
                                      uu____6231 None
                                        t11.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____6253 =
                                      let uu____6255 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort
                                         in
                                      [uu____6255]  in
                                    (uu____6228, uu____6253)  in
                                  Some uu____6222
                              | (uu____6264,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6266)) ->
                                  let uu____6271 =
                                    let uu____6275 =
                                      let uu____6277 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11
                                         in
                                      [uu____6277]  in
                                    (t11, uu____6275)  in
                                  Some uu____6271
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6283),uu____6284) ->
                                  let uu____6289 =
                                    let uu____6293 =
                                      let uu____6295 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21
                                         in
                                      [uu____6295]  in
                                    (t21, uu____6293)  in
                                  Some uu____6289
                              | uu____6300 ->
                                  let uu____6303 =
                                    FStar_Syntax_Util.head_and_args t11  in
                                  (match uu____6303 with
                                   | (head1,uu____6318) ->
                                       let uu____6333 =
                                         let uu____6334 =
                                           FStar_Syntax_Util.un_uinst head1
                                            in
                                         uu____6334.FStar_Syntax_Syntax.n  in
                                       (match uu____6333 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6341;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6343;_}
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
                                        | uu____6352 -> None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6361) ->
                  let uu____6374 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___124_6383  ->
                            match uu___124_6383 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____6388 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____6388 with
                                      | (u',uu____6399) ->
                                          let uu____6414 =
                                            let uu____6415 = whnf env u'  in
                                            uu____6415.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____6414 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____6419) ->
                                               FStar_Unionfind.equivalent uv
                                                 uv'
                                           | uu____6435 -> false))
                                 | uu____6436 -> false)
                            | uu____6438 -> false))
                     in
                  (match uu____6374 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____6459 tps =
                         match uu____6459 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____6486 =
                                    let uu____6491 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound uu____6491  in
                                  (match uu____6486 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____6510 -> None)
                          in
                       let uu____6515 =
                         let uu____6520 =
                           let uu____6524 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (uu____6524, [])  in
                         make_lower_bound uu____6520 lower_bounds  in
                       (match uu____6515 with
                        | None  ->
                            ((let uu____6531 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____6531
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
                            ((let uu____6544 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____6544
                              then
                                let wl' =
                                  let uu___151_6546 = wl  in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___151_6546.wl_deferred);
                                    ctr = (uu___151_6546.ctr);
                                    defer_ok = (uu___151_6546.defer_ok);
                                    smt_ok = (uu___151_6546.smt_ok);
                                    tcenv = (uu___151_6546.tcenv)
                                  }  in
                                let uu____6547 = wl_to_string wl'  in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____6547
                              else ());
                             (let uu____6549 =
                                solve_t env eq_prob
                                  (let uu___152_6550 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___152_6550.wl_deferred);
                                     ctr = (uu___152_6550.ctr);
                                     defer_ok = (uu___152_6550.defer_ok);
                                     smt_ok = (uu___152_6550.smt_ok);
                                     tcenv = (uu___152_6550.tcenv)
                                   })
                                 in
                              match uu____6549 with
                              | Success uu____6552 ->
                                  let wl1 =
                                    let uu___153_6554 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___153_6554.wl_deferred);
                                      ctr = (uu___153_6554.ctr);
                                      defer_ok = (uu___153_6554.defer_ok);
                                      smt_ok = (uu___153_6554.smt_ok);
                                      tcenv = (uu___153_6554.tcenv)
                                    }  in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1
                                     in
                                  let uu____6556 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds
                                     in
                                  Some wl2
                              | uu____6559 -> None))))
              | uu____6560 -> failwith "Impossible: Not a rigid-flex"))

and solve_flex_rigid_join :
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist Prims.option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6567 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____6567
         then
           let uu____6568 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____6568
         else ());
        (let uu____6570 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____6570 with
         | (u,args) ->
             let uu____6597 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____6597 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i  in
                  let base_types_match t1 t2 =
                    let uu____6628 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____6628 with
                    | (h1,args1) ->
                        let uu____6656 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____6656 with
                         | (h2,uu____6669) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____6688 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  if uu____6688
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____6701 =
                                          let uu____6703 =
                                            let uu____6704 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_45  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_45) uu____6704
                                             in
                                          [uu____6703]  in
                                        Some uu____6701))
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
                                       (let uu____6726 =
                                          let uu____6728 =
                                            let uu____6729 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_46  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_46) uu____6729
                                             in
                                          [uu____6728]  in
                                        Some uu____6726))
                                  else None
                              | uu____6737 -> None))
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
                             let uu____6803 =
                               let uu____6809 =
                                 let uu____6812 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21  in
                                 FStar_Syntax_Util.refine x1 uu____6812  in
                               (uu____6809, m1)  in
                             Some uu____6803)
                    | (uu____6821,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____6823)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____6855),uu____6856) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____6887 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6921) ->
                       let uu____6934 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___125_6943  ->
                                 match uu___125_6943 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____6948 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____6948 with
                                           | (u',uu____6959) ->
                                               let uu____6974 =
                                                 let uu____6975 = whnf env u'
                                                    in
                                                 uu____6975.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____6974 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____6979) ->
                                                    FStar_Unionfind.equivalent
                                                      uv uv'
                                                | uu____6995 -> false))
                                      | uu____6996 -> false)
                                 | uu____6998 -> false))
                          in
                       (match uu____6934 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7023 tps =
                              match uu____7023 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7064 =
                                         let uu____7071 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound uu____7071  in
                                       (match uu____7064 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7106 -> None)
                               in
                            let uu____7113 =
                              let uu____7120 =
                                let uu____7126 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (uu____7126, [])  in
                              make_upper_bound uu____7120 upper_bounds  in
                            (match uu____7113 with
                             | None  ->
                                 ((let uu____7135 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____7135
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
                                 ((let uu____7154 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____7154
                                   then
                                     let wl' =
                                       let uu___154_7156 = wl  in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___154_7156.wl_deferred);
                                         ctr = (uu___154_7156.ctr);
                                         defer_ok = (uu___154_7156.defer_ok);
                                         smt_ok = (uu___154_7156.smt_ok);
                                         tcenv = (uu___154_7156.tcenv)
                                       }  in
                                     let uu____7157 = wl_to_string wl'  in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7157
                                   else ());
                                  (let uu____7159 =
                                     solve_t env eq_prob
                                       (let uu___155_7160 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___155_7160.wl_deferred);
                                          ctr = (uu___155_7160.ctr);
                                          defer_ok = (uu___155_7160.defer_ok);
                                          smt_ok = (uu___155_7160.smt_ok);
                                          tcenv = (uu___155_7160.tcenv)
                                        })
                                      in
                                   match uu____7159 with
                                   | Success uu____7162 ->
                                       let wl1 =
                                         let uu___156_7164 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___156_7164.wl_deferred);
                                           ctr = (uu___156_7164.ctr);
                                           defer_ok =
                                             (uu___156_7164.defer_ok);
                                           smt_ok = (uu___156_7164.smt_ok);
                                           tcenv = (uu___156_7164.tcenv)
                                         }  in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1
                                          in
                                       let uu____7166 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds
                                          in
                                       Some wl2
                                   | uu____7169 -> None))))
                   | uu____7170 -> failwith "Impossible: Not a flex-rigid")))

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
                    ((let uu____7235 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____7235
                      then
                        let uu____7236 = prob_to_string env1 rhs_prob  in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7236
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob) Prims.fst  in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___157_7268 = hd1  in
                      let uu____7269 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___157_7268.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___157_7268.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7269
                      }  in
                    let hd21 =
                      let uu___158_7273 = hd2  in
                      let uu____7274 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___158_7273.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___158_7273.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7274
                      }  in
                    let prob =
                      let uu____7278 =
                        let uu____7281 =
                          FStar_All.pipe_left invert_rel (p_rel orig)  in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7281 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter"
                         in
                      FStar_All.pipe_left
                        (fun _0_47  -> FStar_TypeChecker_Common.TProb _0_47)
                        uu____7278
                       in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                    let subst2 =
                      let uu____7289 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1
                         in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7289
                       in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                    let uu____7292 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1  in
                    (match uu____7292 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7310 =
                             FStar_All.pipe_right (p_guard prob) Prims.fst
                              in
                           let uu____7313 =
                             close_forall env2 [(hd12, imp)] phi  in
                           FStar_Syntax_Util.mk_conj uu____7310 uu____7313
                            in
                         ((let uu____7319 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____7319
                           then
                             let uu____7320 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____7321 =
                               FStar_Syntax_Print.bv_to_string hd12  in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7320 uu____7321
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7336 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch"
                 in
              let scope = p_scope orig  in
              let uu____7342 = aux scope env [] bs1 bs2  in
              match uu____7342 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl  in
                  solve env (attempt sub_probs wl1)

and solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7358 = compress_tprob wl problem  in
        solve_t' env uu____7358 wl

and solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7391 = head_matches_delta env1 wl1 t1 t2  in
          match uu____7391 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____7408,uu____7409) ->
                   let may_relate head3 =
                     let uu____7424 =
                       let uu____7425 = FStar_Syntax_Util.un_uinst head3  in
                       uu____7425.FStar_Syntax_Syntax.n  in
                     match uu____7424 with
                     | FStar_Syntax_Syntax.Tm_name _
                       |FStar_Syntax_Syntax.Tm_match _ -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____7431 -> false  in
                   let uu____7432 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok
                      in
                   if uu____7432
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
                                let uu____7449 =
                                  let uu____7450 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____7450 t21
                                   in
                                FStar_Syntax_Util.mk_forall u_x x uu____7449
                             in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1)
                        in
                     let uu____7452 = solve_prob orig (Some guard) [] wl1  in
                     solve env1 uu____7452
                   else giveup env1 "head mismatch" orig
               | (uu____7454,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___159_7462 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___159_7462.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___159_7462.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___159_7462.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___159_7462.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___159_7462.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___159_7462.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___159_7462.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___159_7462.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____7463,None ) ->
                   ((let uu____7470 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____7470
                     then
                       let uu____7471 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____7472 = FStar_Syntax_Print.tag_of_term t1  in
                       let uu____7473 = FStar_Syntax_Print.term_to_string t2
                          in
                       let uu____7474 = FStar_Syntax_Print.tag_of_term t2  in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____7471
                         uu____7472 uu____7473 uu____7474
                     else ());
                    (let uu____7476 = FStar_Syntax_Util.head_and_args t1  in
                     match uu____7476 with
                     | (head11,args1) ->
                         let uu____7502 = FStar_Syntax_Util.head_and_args t2
                            in
                         (match uu____7502 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1  in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____7542 =
                                  let uu____7543 =
                                    FStar_Syntax_Print.term_to_string head11
                                     in
                                  let uu____7544 = args_to_string args1  in
                                  let uu____7545 =
                                    FStar_Syntax_Print.term_to_string head21
                                     in
                                  let uu____7546 = args_to_string args2  in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____7543 uu____7544 uu____7545
                                    uu____7546
                                   in
                                giveup env1 uu____7542 orig
                              else
                                (let uu____7548 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____7551 =
                                        FStar_Syntax_Util.eq_args args1 args2
                                         in
                                      uu____7551 = FStar_Syntax_Util.Equal)
                                    in
                                 if uu____7548
                                 then
                                   let uu____7552 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1
                                      in
                                   match uu____7552 with
                                   | USolved wl2 ->
                                       let uu____7554 =
                                         solve_prob orig None [] wl2  in
                                       solve env1 uu____7554
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____7558 =
                                      base_and_refinement env1 wl1 t1  in
                                    match uu____7558 with
                                    | (base1,refinement1) ->
                                        let uu____7584 =
                                          base_and_refinement env1 wl1 t2  in
                                        (match uu____7584 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____7638 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1
                                                     in
                                                  (match uu____7638 with
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
                                                           (fun uu____7648 
                                                              ->
                                                              fun uu____7649 
                                                                ->
                                                                match 
                                                                  (uu____7648,
                                                                    uu____7649)
                                                                with
                                                                | ((a,uu____7659),
                                                                   (a',uu____7661))
                                                                    ->
                                                                    let uu____7666
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
                                                                    _0_48  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_48)
                                                                    uu____7666)
                                                           args1 args2
                                                          in
                                                       let formula =
                                                         let uu____7672 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                Prims.fst
                                                                  (p_guard p))
                                                             subprobs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____7672
                                                          in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2
                                                          in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____7676 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1)
                                                     in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2)
                                                     in
                                                  solve_t env1
                                                    (let uu___160_7709 =
                                                       problem  in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___160_7709.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___160_7709.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___160_7709.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___160_7709.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___160_7709.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___160_7709.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___160_7709.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___160_7709.FStar_TypeChecker_Common.rank)
                                                     }) wl1))))))))
           in
        let imitate orig env1 wl1 p =
          let uu____7729 = p  in
          match uu____7729 with
          | (((u,k),xs,c),ps,(h,uu____7740,qs)) ->
              let xs1 = sn_binders env1 xs  in
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____7789 = imitation_sub_probs orig env1 xs1 ps qs  in
              (match uu____7789 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____7803 = h gs_xs  in
                     let uu____7804 =
                       let uu____7811 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_49  -> FStar_Util.Inl _0_49)
                          in
                       FStar_All.pipe_right uu____7811
                         (fun _0_50  -> Some _0_50)
                        in
                     FStar_Syntax_Util.abs xs1 uu____7803 uu____7804  in
                   ((let uu____7842 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____7842
                     then
                       let uu____7843 =
                         FStar_Syntax_Print.binders_to_string ", " xs1  in
                       let uu____7844 = FStar_Syntax_Print.comp_to_string c
                          in
                       let uu____7845 = FStar_Syntax_Print.term_to_string im
                          in
                       let uu____7846 = FStar_Syntax_Print.tag_of_term im  in
                       let uu____7847 =
                         let uu____7848 =
                           FStar_List.map (prob_to_string env1) sub_probs  in
                         FStar_All.pipe_right uu____7848
                           (FStar_String.concat ", ")
                          in
                       let uu____7851 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula
                          in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____7843 uu____7844 uu____7845 uu____7846
                         uu____7847 uu____7851
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1
                        in
                     solve env1 (attempt sub_probs wl2))))
           in
        let imitate' orig env1 wl1 uu___126_7869 =
          match uu___126_7869 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p  in
        let project orig env1 wl1 i p =
          let uu____7898 = p  in
          match uu____7898 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____7956 = FStar_List.nth ps i  in
              (match uu____7956 with
               | (pi,uu____7959) ->
                   let uu____7964 = FStar_List.nth xs i  in
                   (match uu____7964 with
                    | (xi,uu____7971) ->
                        let rec gs k =
                          let uu____7980 = FStar_Syntax_Util.arrow_formals k
                             in
                          match uu____7980 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8032)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort
                                       in
                                    let uu____8040 = new_uvar r xs k_a  in
                                    (match uu____8040 with
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
                                         let uu____8059 = aux subst2 tl1  in
                                         (match uu____8059 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8074 =
                                                let uu____8076 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1
                                                   in
                                                uu____8076 :: gi_xs'  in
                                              let uu____8077 =
                                                let uu____8079 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps
                                                   in
                                                uu____8079 :: gi_ps'  in
                                              (uu____8074, uu____8077)))
                                 in
                              aux [] bs
                           in
                        let uu____8082 =
                          let uu____8083 = matches pi  in
                          FStar_All.pipe_left Prims.op_Negation uu____8083
                           in
                        if uu____8082
                        then None
                        else
                          (let uu____8086 = gs xi.FStar_Syntax_Syntax.sort
                              in
                           match uu____8086 with
                           | (g_xs,uu____8093) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                  in
                               let proj =
                                 let uu____8100 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r
                                    in
                                 let uu____8105 =
                                   let uu____8112 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_51  -> FStar_Util.Inl _0_51)
                                      in
                                   FStar_All.pipe_right uu____8112
                                     (fun _0_52  -> Some _0_52)
                                    in
                                 FStar_Syntax_Util.abs xs uu____8100
                                   uu____8105
                                  in
                               let sub1 =
                                 let uu____8143 =
                                   let uu____8146 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r
                                      in
                                   let uu____8153 =
                                     let uu____8156 =
                                       FStar_List.map
                                         (fun uu____8162  ->
                                            match uu____8162 with
                                            | (uu____8167,uu____8168,y) -> y)
                                         qs
                                        in
                                     FStar_All.pipe_left h uu____8156  in
                                   mk_problem (p_scope orig) orig uu____8146
                                     (p_rel orig) uu____8153 None
                                     "projection"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_53  ->
                                      FStar_TypeChecker_Common.TProb _0_53)
                                   uu____8143
                                  in
                               ((let uu____8178 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____8178
                                 then
                                   let uu____8179 =
                                     FStar_Syntax_Print.term_to_string proj
                                      in
                                   let uu____8180 = prob_to_string env1 sub1
                                      in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8179 uu____8180
                                 else ());
                                (let wl2 =
                                   let uu____8183 =
                                     let uu____8185 =
                                       FStar_All.pipe_left Prims.fst
                                         (p_guard sub1)
                                        in
                                     Some uu____8185  in
                                   solve_prob orig uu____8183
                                     [TERM (u, proj)] wl1
                                    in
                                 let uu____8190 =
                                   solve env1 (attempt [sub1] wl2)  in
                                 FStar_All.pipe_left
                                   (fun _0_54  -> Some _0_54) uu____8190)))))
           in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8214 = lhs  in
          match uu____8214 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8237 = FStar_Syntax_Util.arrow_formals_comp k_uv
                   in
                match uu____8237 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8259 =
                        let uu____8285 = decompose env t2  in
                        (((uv, k_uv), xs, c), ps, uu____8285)  in
                      Some uu____8259
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv
                          in
                       let rec elim k args =
                         let uu____8368 =
                           let uu____8372 =
                             let uu____8373 = FStar_Syntax_Subst.compress k
                                in
                             uu____8373.FStar_Syntax_Syntax.n  in
                           (uu____8372, args)  in
                         match uu____8368 with
                         | (uu____8380,[]) ->
                             let uu____8382 =
                               let uu____8388 =
                                 FStar_Syntax_Syntax.mk_Total k  in
                               ([], uu____8388)  in
                             Some uu____8382
                         | (FStar_Syntax_Syntax.Tm_uvar _,_)
                           |(FStar_Syntax_Syntax.Tm_app _,_) ->
                             let uu____8405 =
                               FStar_Syntax_Util.head_and_args k  in
                             (match uu____8405 with
                              | (uv1,uv_args) ->
                                  let uu____8434 =
                                    let uu____8435 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____8435.FStar_Syntax_Syntax.n  in
                                  (match uu____8434 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____8442) ->
                                       let uu____8455 =
                                         pat_vars env [] uv_args  in
                                       (match uu____8455 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____8469  ->
                                                      let uu____8470 =
                                                        let uu____8471 =
                                                          let uu____8472 =
                                                            let uu____8475 =
                                                              let uu____8476
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____8476
                                                                Prims.fst
                                                               in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____8475
                                                             in
                                                          Prims.fst
                                                            uu____8472
                                                           in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____8471
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____8470))
                                               in
                                            let c1 =
                                              let uu____8482 =
                                                let uu____8483 =
                                                  let uu____8486 =
                                                    let uu____8487 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____8487 Prims.fst
                                                     in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____8486
                                                   in
                                                Prims.fst uu____8483  in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____8482
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____8496 =
                                                let uu____8503 =
                                                  let uu____8509 =
                                                    let uu____8510 =
                                                      let uu____8513 =
                                                        let uu____8514 =
                                                          FStar_Syntax_Util.type_u
                                                            ()
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____8514
                                                          Prims.fst
                                                         in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____8513
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____8510
                                                     in
                                                  FStar_Util.Inl uu____8509
                                                   in
                                                Some uu____8503  in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____8496
                                               in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             Some (xs1, c1)))
                                   | uu____8537 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____8542)
                             ->
                             let n_args = FStar_List.length args  in
                             let n_xs = FStar_List.length xs1  in
                             if n_xs = n_args
                             then
                               let uu____8568 =
                                 FStar_Syntax_Subst.open_comp xs1 c1  in
                               FStar_All.pipe_right uu____8568
                                 (fun _0_55  -> Some _0_55)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____8587 =
                                    FStar_Util.first_N n_xs args  in
                                  match uu____8587 with
                                  | (args1,rest) ->
                                      let uu____8603 =
                                        FStar_Syntax_Subst.open_comp xs1 c1
                                         in
                                      (match uu____8603 with
                                       | (xs2,c2) ->
                                           let uu____8611 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest
                                              in
                                           FStar_Util.bind_opt uu____8611
                                             (fun uu____8622  ->
                                                match uu____8622 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____8644 =
                                    FStar_Util.first_N n_args xs1  in
                                  match uu____8644 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____8690 =
                                        let uu____8693 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____8693
                                         in
                                      FStar_All.pipe_right uu____8690
                                        (fun _0_56  -> Some _0_56))
                         | uu____8701 ->
                             let uu____8705 =
                               let uu____8706 =
                                 FStar_Syntax_Print.uvar_to_string uv  in
                               let uu____8710 =
                                 FStar_Syntax_Print.term_to_string k  in
                               let uu____8711 =
                                 FStar_Syntax_Print.term_to_string k_uv1  in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____8706 uu____8710 uu____8711
                                in
                             failwith uu____8705
                          in
                       let uu____8715 = elim k_uv1 ps  in
                       FStar_Util.bind_opt uu____8715
                         (fun uu____8743  ->
                            match uu____8743 with
                            | (xs1,c1) ->
                                let uu____8771 =
                                  let uu____8794 = decompose env t2  in
                                  (((uv, k_uv1), xs1, c1), ps, uu____8794)
                                   in
                                Some uu____8771))
                 in
              let rec imitate_or_project n1 stopt i =
                if (i >= n1) || (FStar_Option.isNone stopt)
                then
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig
                else
                  (let st = FStar_Option.get stopt  in
                   let tx = FStar_Unionfind.new_transaction ()  in
                   if i = (~- (Prims.parse_int "1"))
                   then
                     let uu____8866 = imitate orig env wl1 st  in
                     match uu____8866 with
                     | Failed uu____8871 ->
                         (FStar_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____8877 = project orig env wl1 i st  in
                      match uu____8877 with
                      | None |Some (Failed _) ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol))
                 in
              let check_head fvs1 t21 =
                let uu____8895 = FStar_Syntax_Util.head_and_args t21  in
                match uu____8895 with
                | (hd1,uu____8906) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow _
                       |FStar_Syntax_Syntax.Tm_constant _
                        |FStar_Syntax_Syntax.Tm_abs _ -> true
                     | uu____8924 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1  in
                         let uu____8927 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1  in
                         if uu____8927
                         then true
                         else
                           ((let uu____8930 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____8930
                             then
                               let uu____8931 = names_to_string fvs_hd  in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____8931
                             else ());
                            false))
                 in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____8939 =
                    let uu____8942 = FStar_Syntax_Util.head_and_args t21  in
                    FStar_All.pipe_right uu____8942 Prims.fst  in
                  FStar_All.pipe_right uu____8939 FStar_Syntax_Free.names  in
                let uu____8973 = FStar_Util.set_is_empty fvs_hd  in
                if uu____8973
                then ~- (Prims.parse_int "1")
                else (Prims.parse_int "0")  in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1  in
                   let t21 = sn env t2  in
                   let fvs1 = FStar_Syntax_Free.names t11  in
                   let fvs2 = FStar_Syntax_Free.names t21  in
                   let uu____8982 = occurs_check env wl1 (uv, k_uv) t21  in
                   (match uu____8982 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____8990 =
                            let uu____8991 = FStar_Option.get msg  in
                            Prims.strcat "occurs-check failed: " uu____8991
                             in
                          giveup_or_defer1 orig uu____8990
                        else
                          (let uu____8993 =
                             FStar_Util.set_is_subset_of fvs2 fvs1  in
                           if uu____8993
                           then
                             let uu____8994 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
                                in
                             (if uu____8994
                              then
                                let uu____8995 = subterms args_lhs  in
                                imitate' orig env wl1 uu____8995
                              else
                                ((let uu____8999 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____8999
                                  then
                                    let uu____9000 =
                                      FStar_Syntax_Print.term_to_string t11
                                       in
                                    let uu____9001 = names_to_string fvs1  in
                                    let uu____9002 = names_to_string fvs2  in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9000 uu____9001 uu____9002
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9007 ->
                                        let uu____9008 = sn_binders env vars
                                           in
                                        u_abs k_uv uu____9008 t21
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
                               (let uu____9017 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21)
                                   in
                                if uu____9017
                                then
                                  ((let uu____9019 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____9019
                                    then
                                      let uu____9020 =
                                        FStar_Syntax_Print.term_to_string t11
                                         in
                                      let uu____9021 = names_to_string fvs1
                                         in
                                      let uu____9022 = names_to_string fvs2
                                         in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9020 uu____9021 uu____9022
                                    else ());
                                   (let uu____9024 = subterms args_lhs  in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9024
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
                     (let uu____9035 =
                        let uu____9036 = FStar_Syntax_Free.names t1  in
                        check_head uu____9036 t2  in
                      if uu____9035
                      then
                        let im_ok = imitate_ok t2  in
                        ((let uu____9040 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel")
                             in
                          if uu____9040
                          then
                            let uu____9041 =
                              FStar_Syntax_Print.term_to_string t1  in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9041
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9044 = subterms args_lhs  in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9044 im_ok))
                      else giveup env "head-symbol is free" orig))
           in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9086 =
               match uu____9086 with
               | (t,u,k,args) ->
                   let uu____9116 = FStar_Syntax_Util.arrow_formals k  in
                   (match uu____9116 with
                    | (all_formals,uu____9127) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____9219  ->
                                        match uu____9219 with
                                        | (x,imp) ->
                                            let uu____9226 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            (uu____9226, imp)))
                                 in
                              let pattern_vars1 = FStar_List.rev pattern_vars
                                 in
                              let kk =
                                let uu____9234 = FStar_Syntax_Util.type_u ()
                                   in
                                match uu____9234 with
                                | (t1,uu____9238) ->
                                    let uu____9239 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1
                                       in
                                    Prims.fst uu____9239
                                 in
                              let uu____9242 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk
                                 in
                              (match uu____9242 with
                               | (t',tm_u1) ->
                                   let uu____9249 = destruct_flex_t t'  in
                                   (match uu____9249 with
                                    | (uu____9269,u1,k1,uu____9272) ->
                                        let sol =
                                          let uu____9300 =
                                            let uu____9305 =
                                              u_abs k all_formals t'  in
                                            ((u, k), uu____9305)  in
                                          TERM uu____9300  in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos
                                           in
                                        (sol, (t_app, u1, k1, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____9365 = pat_var_opt env pat_args hd1
                                 in
                              (match uu____9365 with
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
                                              (fun uu____9394  ->
                                                 match uu____9394 with
                                                 | (x,uu____9398) ->
                                                     FStar_Syntax_Syntax.bv_eq
                                                       x (Prims.fst y)))
                                      in
                                   if Prims.op_Negation maybe_pat
                                   then
                                     aux pat_args pattern_vars
                                       pattern_var_set formals1 tl1
                                   else
                                     (let fvs =
                                        FStar_Syntax_Free.names
                                          (Prims.fst y).FStar_Syntax_Syntax.sort
                                         in
                                      let uu____9404 =
                                        let uu____9405 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set
                                           in
                                        Prims.op_Negation uu____9405  in
                                      if uu____9404
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____9409 =
                                           FStar_Util.set_add
                                             (Prims.fst formal)
                                             pattern_var_set
                                            in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____9409 formals1
                                           tl1)))
                          | uu____9415 -> failwith "Impossible"  in
                        let uu____9426 = FStar_Syntax_Syntax.new_bv_set ()
                           in
                        aux [] [] uu____9426 all_formals args)
                in
             let solve_both_pats wl1 uu____9474 uu____9475 r =
               match (uu____9474, uu____9475) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____9629 =
                     (FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)
                      in
                   if uu____9629
                   then
                     let uu____9633 = solve_prob orig None [] wl1  in
                     solve env uu____9633
                   else
                     (let xs1 = sn_binders env xs  in
                      let ys1 = sn_binders env ys  in
                      let zs = intersect_vars xs1 ys1  in
                      (let uu____9648 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____9648
                       then
                         let uu____9649 =
                           FStar_Syntax_Print.binders_to_string ", " xs1  in
                         let uu____9650 =
                           FStar_Syntax_Print.binders_to_string ", " ys1  in
                         let uu____9651 =
                           FStar_Syntax_Print.binders_to_string ", " zs  in
                         let uu____9652 =
                           FStar_Syntax_Print.term_to_string k1  in
                         let uu____9653 =
                           FStar_Syntax_Print.term_to_string k2  in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____9649 uu____9650 uu____9651 uu____9652
                           uu____9653
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2  in
                         let args_len = FStar_List.length args  in
                         if xs_len = args_len
                         then
                           let uu____9695 =
                             FStar_Syntax_Util.subst_of_list xs2 args  in
                           FStar_Syntax_Subst.subst uu____9695 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____9703 =
                                FStar_Util.first_N args_len xs2  in
                              match uu____9703 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____9733 =
                                      FStar_Syntax_Syntax.mk_GTotal k  in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____9733
                                     in
                                  let uu____9736 =
                                    FStar_Syntax_Util.subst_of_list xs3 args
                                     in
                                  FStar_Syntax_Subst.subst uu____9736 k3)
                           else
                             (let uu____9739 =
                                let uu____9740 =
                                  FStar_Syntax_Print.term_to_string k  in
                                let uu____9741 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2
                                   in
                                let uu____9742 =
                                  FStar_Syntax_Print.args_to_string args  in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____9740 uu____9741 uu____9742
                                 in
                              failwith uu____9739)
                          in
                       let uu____9743 =
                         let uu____9749 =
                           let uu____9757 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1
                              in
                           FStar_Syntax_Util.arrow_formals uu____9757  in
                         match uu____9749 with
                         | (bs,k1') ->
                             let uu____9775 =
                               let uu____9783 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2
                                  in
                               FStar_Syntax_Util.arrow_formals uu____9783  in
                             (match uu____9775 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1  in
                                  let k2'_ys = subst_k k2' cs args2  in
                                  let sub_prob =
                                    let uu____9804 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_57  ->
                                         FStar_TypeChecker_Common.TProb _0_57)
                                      uu____9804
                                     in
                                  let uu____9809 =
                                    let uu____9812 =
                                      let uu____9813 =
                                        FStar_Syntax_Subst.compress k1'  in
                                      uu____9813.FStar_Syntax_Syntax.n  in
                                    let uu____9816 =
                                      let uu____9817 =
                                        FStar_Syntax_Subst.compress k2'  in
                                      uu____9817.FStar_Syntax_Syntax.n  in
                                    (uu____9812, uu____9816)  in
                                  (match uu____9809 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____9825,uu____9826) ->
                                       (k1', [sub_prob])
                                   | (uu____9830,FStar_Syntax_Syntax.Tm_type
                                      uu____9831) -> (k2', [sub_prob])
                                   | uu____9835 ->
                                       let uu____9838 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____9838 with
                                        | (t,uu____9847) ->
                                            let uu____9848 = new_uvar r zs t
                                               in
                                            (match uu____9848 with
                                             | (k_zs,uu____9857) ->
                                                 let kprob =
                                                   let uu____9859 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding"
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_58  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_58) uu____9859
                                                    in
                                                 (k_zs, [sub_prob; kprob])))))
                          in
                       match uu____9743 with
                       | (k_u',sub_probs) ->
                           let uu____9873 =
                             let uu____9881 =
                               let uu____9882 = new_uvar r zs k_u'  in
                               FStar_All.pipe_left Prims.fst uu____9882  in
                             let uu____9887 =
                               let uu____9890 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow xs1 uu____9890  in
                             let uu____9893 =
                               let uu____9896 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow ys1 uu____9896  in
                             (uu____9881, uu____9887, uu____9893)  in
                           (match uu____9873 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs  in
                                let uu____9915 =
                                  occurs_check env wl1 (u1, k1) sub1  in
                                (match uu____9915 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1)  in
                                        let uu____9939 =
                                          FStar_Unionfind.equivalent u1 u2
                                           in
                                        if uu____9939
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1
                                             in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs
                                              in
                                           let uu____9946 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2
                                              in
                                           match uu____9946 with
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
             let solve_one_pat uu____9998 uu____9999 =
               match (uu____9998, uu____9999) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10103 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____10103
                     then
                       let uu____10104 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____10105 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10104 uu____10105
                     else ());
                    (let uu____10107 = FStar_Unionfind.equivalent u1 u2  in
                     if uu____10107
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10117  ->
                              fun uu____10118  ->
                                match (uu____10117, uu____10118) with
                                | ((a,uu____10128),(t21,uu____10130)) ->
                                    let uu____10135 =
                                      let uu____10138 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      mk_problem (p_scope orig) orig
                                        uu____10138
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index"
                                       in
                                    FStar_All.pipe_right uu____10135
                                      (fun _0_59  ->
                                         FStar_TypeChecker_Common.TProb _0_59))
                           xs args2
                          in
                       let guard =
                         let uu____10142 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p) Prims.fst)
                             sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____10142  in
                       let wl1 = solve_prob orig (Some guard) [] wl  in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2  in
                        let rhs_vars = FStar_Syntax_Free.names t21  in
                        let uu____10152 = occurs_check env wl (u1, k1) t21
                           in
                        match uu____10152 with
                        | (occurs_ok,uu____10161) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs  in
                            let uu____10166 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars)
                               in
                            if uu____10166
                            then
                              let sol =
                                let uu____10168 =
                                  let uu____10173 = u_abs k1 xs t21  in
                                  ((u1, k1), uu____10173)  in
                                TERM uu____10168  in
                              let wl1 = solve_prob orig None [sol] wl  in
                              solve env wl1
                            else
                              (let uu____10186 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok)
                                  in
                               if uu____10186
                               then
                                 let uu____10187 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2)
                                    in
                                 match uu____10187 with
                                 | (sol,(uu____10201,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl
                                        in
                                     ((let uu____10211 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern")
                                          in
                                       if uu____10211
                                       then
                                         let uu____10212 =
                                           uvi_to_string env sol  in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10212
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____10217 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint"))))
                in
             let uu____10219 = lhs  in
             match uu____10219 with
             | (t1,u1,k1,args1) ->
                 let uu____10224 = rhs  in
                 (match uu____10224 with
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
                       | uu____10250 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____10256 =
                                force_quasi_pattern None (t1, u1, k1, args1)
                                 in
                              match uu____10256 with
                              | (sol,uu____10263) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl  in
                                  ((let uu____10266 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern")
                                       in
                                    if uu____10266
                                    then
                                      let uu____10267 = uvi_to_string env sol
                                         in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____10267
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____10272 ->
                                        giveup env "impossible" orig))))))
           in
        let orig = FStar_TypeChecker_Common.TProb problem  in
        let uu____10274 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs
           in
        if uu____10274
        then
          let uu____10275 = solve_prob orig None [] wl  in
          solve env uu____10275
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs  in
           let t2 = problem.FStar_TypeChecker_Common.rhs  in
           let uu____10279 = FStar_Util.physical_equality t1 t2  in
           if uu____10279
           then
             let uu____10280 = solve_prob orig None [] wl  in
             solve env uu____10280
           else
             ((let uu____10283 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck")
                  in
               if uu____10283
               then
                 let uu____10284 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid
                    in
                 FStar_Util.print1 "Attempting %s\n" uu____10284
               else ());
              (let r = FStar_TypeChecker_Env.get_range env  in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar _,_)
                 |(_,FStar_Syntax_Syntax.Tm_bvar _) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___127_10330 =
                     match uu___127_10330 with
                     | [] -> c
                     | bs ->
                         let uu____10344 =
                           (FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))) None
                             c.FStar_Syntax_Syntax.pos
                            in
                         FStar_Syntax_Syntax.mk_Total uu____10344
                      in
                   let uu____10358 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                   (match uu____10358 with
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
                                   let uu____10444 =
                                     FStar_Options.use_eq_at_higher_order ()
                                      in
                                   if uu____10444
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation
                                    in
                                 let uu____10446 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_TypeChecker_Common.CProb _0_60)
                                   uu____10446))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___128_10523 =
                     match uu___128_10523 with
                     | [] -> t
                     | bs ->
                         (FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs (bs, t, l))) None
                           t.FStar_Syntax_Syntax.pos
                      in
                   let uu____10562 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2))
                      in
                   (match uu____10562 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____10645 =
                                   let uu____10648 =
                                     FStar_Syntax_Subst.subst subst1 tbody11
                                      in
                                   let uu____10649 =
                                     FStar_Syntax_Subst.subst subst1 tbody21
                                      in
                                   mk_problem scope orig uu____10648
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____10649 None "lambda co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.TProb _0_61)
                                   uu____10645))
               | (FStar_Syntax_Syntax.Tm_abs _,_)
                 |(_,FStar_Syntax_Syntax.Tm_abs _) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____10664 -> true
                     | uu____10679 -> false  in
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
                   let uu____10707 =
                     let uu____10718 = maybe_eta t1  in
                     let uu____10723 = maybe_eta t2  in
                     (uu____10718, uu____10723)  in
                   (match uu____10707 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___161_10754 = problem  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___161_10754.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___161_10754.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___161_10754.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___161_10754.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___161_10754.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___161_10754.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___161_10754.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___161_10754.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs)
                      |(FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____10787 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____10787
                        then
                          let uu____10788 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____10788 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____10793 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____10804,FStar_Syntax_Syntax.Tm_refine uu____10805) ->
                   let uu____10814 = as_refinement env wl t1  in
                   (match uu____10814 with
                    | (x1,phi1) ->
                        let uu____10819 = as_refinement env wl t2  in
                        (match uu____10819 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____10825 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_62  ->
                                    FStar_TypeChecker_Common.TProb _0_62)
                                 uu____10825
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
                               let uu____10858 = imp phi12 phi22  in
                               FStar_All.pipe_right uu____10858
                                 (guard_on_element wl problem x11)
                                in
                             let fallback uu____10862 =
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
                                 let uu____10868 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     Prims.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____10868 impl
                                  in
                               let wl1 = solve_prob orig (Some guard) [] wl
                                  in
                               solve env1 (attempt [base_prob] wl1)  in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____10875 =
                                   let uu____10878 =
                                     let uu____10879 =
                                       FStar_Syntax_Syntax.mk_binder x11  in
                                     uu____10879 :: (p_scope orig)  in
                                   mk_problem uu____10878 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_63  ->
                                      FStar_TypeChecker_Common.TProb _0_63)
                                   uu____10875
                                  in
                               let uu____10882 =
                                 solve env1
                                   (let uu___162_10883 = wl  in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___162_10883.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___162_10883.smt_ok);
                                      tcenv = (uu___162_10883.tcenv)
                                    })
                                  in
                               (match uu____10882 with
                                | Failed uu____10887 -> fallback ()
                                | Success uu____10890 ->
                                    let guard =
                                      let uu____10894 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob) Prims.fst
                                         in
                                      let uu____10897 =
                                        let uu____10898 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob) Prims.fst
                                           in
                                        FStar_All.pipe_right uu____10898
                                          (guard_on_element wl problem x11)
                                         in
                                      FStar_Syntax_Util.mk_conj uu____10894
                                        uu____10897
                                       in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl  in
                                    let wl2 =
                                      let uu___163_10905 = wl1  in
                                      {
                                        attempting =
                                          (uu___163_10905.attempting);
                                        wl_deferred =
                                          (uu___163_10905.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___163_10905.defer_ok);
                                        smt_ok = (uu___163_10905.smt_ok);
                                        tcenv = (uu___163_10905.tcenv)
                                      }  in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar _,FStar_Syntax_Syntax.Tm_uvar
                  _)
                 |(FStar_Syntax_Syntax.Tm_app
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_),FStar_Syntax_Syntax.Tm_uvar
                   _)
                  |(FStar_Syntax_Syntax.Tm_uvar _,FStar_Syntax_Syntax.Tm_app
                    ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                       FStar_Syntax_Syntax.tk = _;
                       FStar_Syntax_Syntax.pos = _;
                       FStar_Syntax_Syntax.vars = _;_},_))
                   |(FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                        FStar_Syntax_Syntax.tk = _;
                        FStar_Syntax_Syntax.pos = _;
                        FStar_Syntax_Syntax.vars = _;_},_),FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                        FStar_Syntax_Syntax.tk = _;
                        FStar_Syntax_Syntax.pos = _;
                        FStar_Syntax_Syntax.vars = _;_},_))
                   ->
                   let uu____10959 = destruct_flex_t t1  in
                   let uu____10960 = destruct_flex_t t2  in
                   flex_flex1 orig uu____10959 uu____10960
               | (FStar_Syntax_Syntax.Tm_uvar _,_)
                 |(FStar_Syntax_Syntax.Tm_app
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_),_)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____10976 = destruct_flex_pattern env t1  in
                   solve_t_flex_rigid false orig uu____10976 t2 wl
               | (_,FStar_Syntax_Syntax.Tm_uvar _)
                 |(_,FStar_Syntax_Syntax.Tm_app
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar _,FStar_Syntax_Syntax.Tm_type
                  _)
                 |(FStar_Syntax_Syntax.Tm_app
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_),FStar_Syntax_Syntax.Tm_type
                   _)
                  |(FStar_Syntax_Syntax.Tm_uvar
                    _,FStar_Syntax_Syntax.Tm_arrow _)
                   |(FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                        FStar_Syntax_Syntax.tk = _;
                        FStar_Syntax_Syntax.pos = _;
                        FStar_Syntax_Syntax.vars = _;_},_),FStar_Syntax_Syntax.Tm_arrow
                     _)
                   ->
                   solve_t' env
                     (let uu___164_11025 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___164_11025.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___164_11025.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___164_11025.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___164_11025.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___164_11025.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___164_11025.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___164_11025.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___164_11025.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___164_11025.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar _,_)
                 |(FStar_Syntax_Syntax.Tm_app
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_),_)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation
                         in
                      let uu____11043 =
                        let uu____11044 = is_top_level_prob orig  in
                        FStar_All.pipe_left Prims.op_Negation uu____11044  in
                      if uu____11043
                      then
                        let uu____11045 =
                          FStar_All.pipe_left
                            (fun _0_64  ->
                               FStar_TypeChecker_Common.TProb _0_64)
                            (let uu___165_11048 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___165_11048.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___165_11048.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___165_11048.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___165_11048.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___165_11048.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___165_11048.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___165_11048.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___165_11048.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___165_11048.FStar_TypeChecker_Common.rank)
                             })
                           in
                        let uu____11049 = destruct_flex_pattern env t1  in
                        solve_t_flex_rigid false uu____11045 uu____11049 t2
                          wl
                      else
                        (let uu____11054 = base_and_refinement env wl t2  in
                         match uu____11054 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____11084 =
                                    FStar_All.pipe_left
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65)
                                      (let uu___166_11087 = problem  in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___166_11087.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___166_11087.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___166_11087.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___166_11087.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___166_11087.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___166_11087.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___166_11087.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___166_11087.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___166_11087.FStar_TypeChecker_Common.rank)
                                       })
                                     in
                                  let uu____11088 =
                                    destruct_flex_pattern env t1  in
                                  solve_t_flex_rigid false uu____11084
                                    uu____11088 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___167_11103 = y  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___167_11103.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___167_11103.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }  in
                                  let impl =
                                    guard_on_element wl problem y' phi  in
                                  let base_prob =
                                    let uu____11106 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_66  ->
                                         FStar_TypeChecker_Common.TProb _0_66)
                                      uu____11106
                                     in
                                  let guard =
                                    let uu____11114 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob) Prims.fst
                                       in
                                    FStar_Syntax_Util.mk_conj uu____11114
                                      impl
                                     in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl  in
                                  solve env (attempt [base_prob] wl1))))
               | (_,FStar_Syntax_Syntax.Tm_uvar _)
                 |(_,FStar_Syntax_Syntax.Tm_app
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____11136 = base_and_refinement env wl t1  in
                      match uu____11136 with
                      | (t_base,uu____11147) ->
                          solve_t env
                            (let uu___168_11162 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_11162.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_11162.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_11162.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_11162.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___168_11162.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_11162.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_11162.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_11162.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____11165,uu____11166) ->
                   let t21 =
                     let uu____11174 = base_and_refinement env wl t2  in
                     FStar_All.pipe_left force_refinement uu____11174  in
                   solve_t env
                     (let uu___169_11187 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_11187.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_11187.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___169_11187.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___169_11187.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_11187.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_11187.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_11187.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_11187.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_11187.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____11188,FStar_Syntax_Syntax.Tm_refine uu____11189) ->
                   let t11 =
                     let uu____11197 = base_and_refinement env wl t1  in
                     FStar_All.pipe_left force_refinement uu____11197  in
                   solve_t env
                     (let uu___170_11210 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___170_11210.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___170_11210.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___170_11210.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___170_11210.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___170_11210.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___170_11210.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___170_11210.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___170_11210.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___170_11210.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match _,_)
                 |(FStar_Syntax_Syntax.Tm_uinst _,_)
                  |(FStar_Syntax_Syntax.Tm_name _,_)
                   |(FStar_Syntax_Syntax.Tm_constant _,_)
                    |(FStar_Syntax_Syntax.Tm_fvar _,_)
                     |(FStar_Syntax_Syntax.Tm_app _,_)
                      |(_,FStar_Syntax_Syntax.Tm_match _)
                       |(_,FStar_Syntax_Syntax.Tm_uinst _)
                        |(_,FStar_Syntax_Syntax.Tm_name _)
                         |(_,FStar_Syntax_Syntax.Tm_constant _)
                          |(_,FStar_Syntax_Syntax.Tm_fvar _)
                           |(_,FStar_Syntax_Syntax.Tm_app _)
                   ->
                   let head1 =
                     let uu____11240 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____11240 Prims.fst  in
                   let head2 =
                     let uu____11271 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____11271 Prims.fst  in
                   let uu____11299 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____11299
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____11308 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____11308
                      then
                        let guard =
                          let uu____11315 =
                            let uu____11316 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____11316 = FStar_Syntax_Util.Equal  in
                          if uu____11315
                          then None
                          else
                            (let uu____11319 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_67  -> Some _0_67)
                               uu____11319)
                           in
                        let uu____11321 = solve_prob orig guard [] wl  in
                        solve env uu____11321
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____11325,uu____11326),uu____11327) ->
                   solve_t' env
                     (let uu___171_11356 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___171_11356.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___171_11356.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___171_11356.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___171_11356.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___171_11356.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___171_11356.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___171_11356.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___171_11356.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___171_11356.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____11359,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____11361,uu____11362)) ->
                   solve_t' env
                     (let uu___172_11391 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___172_11391.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___172_11391.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___172_11391.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___172_11391.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___172_11391.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___172_11391.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___172_11391.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___172_11391.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___172_11391.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let _,_)
                 |(FStar_Syntax_Syntax.Tm_meta _,_)
                  |(FStar_Syntax_Syntax.Tm_delayed _,_)
                   |(_,FStar_Syntax_Syntax.Tm_meta _)
                    |(_,FStar_Syntax_Syntax.Tm_delayed _)
                     |(_,FStar_Syntax_Syntax.Tm_let _)
                   ->
                   let uu____11404 =
                     let uu____11405 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____11406 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____11405
                       uu____11406
                      in
                   failwith uu____11404
               | uu____11407 -> giveup env "head tag mismatch" orig)))

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
          (let uu____11439 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____11439
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____11447  ->
                  fun uu____11448  ->
                    match (uu____11447, uu____11448) with
                    | ((a1,uu____11458),(a2,uu____11460)) ->
                        let uu____11465 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg"
                           in
                        FStar_All.pipe_left
                          (fun _0_68  -> FStar_TypeChecker_Common.TProb _0_68)
                          uu____11465)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args
              in
           let guard =
             let uu____11471 =
               FStar_List.map
                 (fun p  -> FStar_All.pipe_right (p_guard p) Prims.fst)
                 sub_probs
                in
             FStar_Syntax_Util.mk_conj_l uu____11471  in
           let wl1 = solve_prob orig (Some guard) [] wl  in
           solve env (attempt sub_probs wl1))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____11491 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____11498)::[] -> wp1
              | uu____11511 ->
                  let uu____11517 =
                    let uu____11518 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name)
                       in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____11518
                     in
                  failwith uu____11517
               in
            let uu____11521 =
              let uu____11527 =
                let uu____11528 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____11528  in
              [uu____11527]  in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____11521;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____11529 = lift_c1 ()  in solve_eq uu____11529 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___129_11533  ->
                       match uu___129_11533 with
                       | FStar_Syntax_Syntax.TOTAL 
                         |FStar_Syntax_Syntax.MLEFFECT 
                          |FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____11534 -> false))
                in
             let uu____11535 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____11559)::uu____11560,(wp2,uu____11562)::uu____11563)
                   -> (wp1, wp2)
               | uu____11604 ->
                   let uu____11617 =
                     let uu____11618 =
                       let uu____11621 =
                         let uu____11622 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____11623 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____11622 uu____11623
                          in
                       (uu____11621, (env.FStar_TypeChecker_Env.range))  in
                     FStar_Errors.Error uu____11618  in
                   Prims.raise uu____11617
                in
             match uu____11535 with
             | (wpc1,wpc2) ->
                 let uu____11640 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____11640
                 then
                   let uu____11643 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type"
                      in
                   solve_t env uu____11643 wl
                 else
                   (let c2_decl =
                      FStar_TypeChecker_Env.get_effect_decl env
                        c21.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____11648 =
                      FStar_All.pipe_right
                        c2_decl.FStar_Syntax_Syntax.qualifiers
                        (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                       in
                    if uu____11648
                    then
                      let c1_repr =
                        let uu____11651 =
                          let uu____11652 =
                            let uu____11653 = lift_c1 ()  in
                            FStar_Syntax_Syntax.mk_Comp uu____11653  in
                          let uu____11654 =
                            env.FStar_TypeChecker_Env.universe_of env
                              c11.FStar_Syntax_Syntax.result_typ
                             in
                          FStar_TypeChecker_Env.reify_comp env uu____11652
                            uu____11654
                           in
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant;
                          FStar_TypeChecker_Normalize.WHNF] env uu____11651
                         in
                      let c2_repr =
                        let uu____11656 =
                          let uu____11657 = FStar_Syntax_Syntax.mk_Comp c21
                             in
                          let uu____11658 =
                            env.FStar_TypeChecker_Env.universe_of env
                              c21.FStar_Syntax_Syntax.result_typ
                             in
                          FStar_TypeChecker_Env.reify_comp env uu____11657
                            uu____11658
                           in
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant;
                          FStar_TypeChecker_Normalize.WHNF] env uu____11656
                         in
                      let prob =
                        let uu____11660 =
                          let uu____11663 =
                            let uu____11664 =
                              FStar_Syntax_Print.term_to_string c1_repr  in
                            let uu____11665 =
                              FStar_Syntax_Print.term_to_string c2_repr  in
                            FStar_Util.format2 "sub effect repr: %s <: %s"
                              uu____11664 uu____11665
                             in
                          sub_prob c1_repr
                            problem.FStar_TypeChecker_Common.relation c2_repr
                            uu____11663
                           in
                        FStar_TypeChecker_Common.TProb uu____11660  in
                      let wl1 =
                        let uu____11667 =
                          let uu____11669 =
                            FStar_All.pipe_right (p_guard prob) Prims.fst  in
                          Some uu____11669  in
                        solve_prob orig uu____11667 [] wl  in
                      solve env (attempt [prob] wl1)
                    else
                      (let g =
                         if env.FStar_TypeChecker_Env.lax
                         then FStar_Syntax_Util.t_true
                         else
                           if is_null_wp_2
                           then
                             ((let uu____11676 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "Rel")
                                  in
                               if uu____11676
                               then
                                 FStar_Util.print_string
                                   "Using trivial wp ... \n"
                               else ());
                              (let uu____11678 =
                                 let uu____11681 =
                                   let uu____11682 =
                                     let uu____11692 =
                                       let uu____11693 =
                                         let uu____11694 =
                                           env.FStar_TypeChecker_Env.universe_of
                                             env
                                             c11.FStar_Syntax_Syntax.result_typ
                                            in
                                         [uu____11694]  in
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         uu____11693 env c2_decl
                                         c2_decl.FStar_Syntax_Syntax.trivial
                                        in
                                     let uu____11695 =
                                       let uu____11697 =
                                         FStar_Syntax_Syntax.as_arg
                                           c11.FStar_Syntax_Syntax.result_typ
                                          in
                                       let uu____11698 =
                                         let uu____11700 =
                                           let uu____11701 =
                                             (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                               c11.FStar_Syntax_Syntax.result_typ
                                               wpc1
                                              in
                                           FStar_All.pipe_left
                                             FStar_Syntax_Syntax.as_arg
                                             uu____11701
                                            in
                                         [uu____11700]  in
                                       uu____11697 :: uu____11698  in
                                     (uu____11692, uu____11695)  in
                                   FStar_Syntax_Syntax.Tm_app uu____11682  in
                                 FStar_Syntax_Syntax.mk uu____11681  in
                               uu____11678
                                 (Some
                                    (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                 r))
                           else
                             (let uu____11712 =
                                let uu____11715 =
                                  let uu____11716 =
                                    let uu____11726 =
                                      let uu____11727 =
                                        let uu____11728 =
                                          env.FStar_TypeChecker_Env.universe_of
                                            env
                                            c21.FStar_Syntax_Syntax.result_typ
                                           in
                                        [uu____11728]  in
                                      FStar_TypeChecker_Env.inst_effect_fun_with
                                        uu____11727 env c2_decl
                                        c2_decl.FStar_Syntax_Syntax.stronger
                                       in
                                    let uu____11729 =
                                      let uu____11731 =
                                        FStar_Syntax_Syntax.as_arg
                                          c21.FStar_Syntax_Syntax.result_typ
                                         in
                                      let uu____11732 =
                                        let uu____11734 =
                                          FStar_Syntax_Syntax.as_arg wpc2  in
                                        let uu____11735 =
                                          let uu____11737 =
                                            let uu____11738 =
                                              (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                c11.FStar_Syntax_Syntax.result_typ
                                                wpc1
                                               in
                                            FStar_All.pipe_left
                                              FStar_Syntax_Syntax.as_arg
                                              uu____11738
                                             in
                                          [uu____11737]  in
                                        uu____11734 :: uu____11735  in
                                      uu____11731 :: uu____11732  in
                                    (uu____11726, uu____11729)  in
                                  FStar_Syntax_Syntax.Tm_app uu____11716  in
                                FStar_Syntax_Syntax.mk uu____11715  in
                              uu____11712
                                (Some
                                   (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                r)
                          in
                       let base_prob =
                         let uu____11749 =
                           sub_prob c11.FStar_Syntax_Syntax.result_typ
                             problem.FStar_TypeChecker_Common.relation
                             c21.FStar_Syntax_Syntax.result_typ "result type"
                            in
                         FStar_All.pipe_left
                           (fun _0_69  ->
                              FStar_TypeChecker_Common.TProb _0_69)
                           uu____11749
                          in
                       let wl1 =
                         let uu____11755 =
                           let uu____11757 =
                             let uu____11760 =
                               FStar_All.pipe_right (p_guard base_prob)
                                 Prims.fst
                                in
                             FStar_Syntax_Util.mk_conj uu____11760 g  in
                           FStar_All.pipe_left (fun _0_70  -> Some _0_70)
                             uu____11757
                            in
                         solve_prob orig uu____11755 [] wl  in
                       solve env (attempt [base_prob] wl1))))
           in
        let uu____11770 = FStar_Util.physical_equality c1 c2  in
        if uu____11770
        then
          let uu____11771 = solve_prob orig None [] wl  in
          solve env uu____11771
        else
          ((let uu____11774 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____11774
            then
              let uu____11775 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____11776 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____11775
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____11776
            else ());
           (let uu____11778 =
              let uu____11781 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____11782 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____11781, uu____11782)  in
            match uu____11778 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____11786),FStar_Syntax_Syntax.Total
                    (t2,uu____11788)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____11801 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type"
                        in
                     solve_t env uu____11801 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____11804,FStar_Syntax_Syntax.Total uu____11805) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,_),FStar_Syntax_Syntax.Total (t2,_))
                   |(FStar_Syntax_Syntax.GTotal
                     (t1,_),FStar_Syntax_Syntax.GTotal (t2,_))
                    |(FStar_Syntax_Syntax.Total
                      (t1,_),FStar_Syntax_Syntax.GTotal (t2,_))
                     ->
                     let uu____11854 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type"
                        in
                     solve_t env uu____11854 wl
                 | (FStar_Syntax_Syntax.GTotal _,FStar_Syntax_Syntax.Comp _)
                   |(FStar_Syntax_Syntax.Total _,FStar_Syntax_Syntax.Comp _)
                     ->
                     let uu____11861 =
                       let uu___173_11864 = problem  in
                       let uu____11867 =
                         let uu____11868 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____11868
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___173_11864.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____11867;
                         FStar_TypeChecker_Common.relation =
                           (uu___173_11864.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___173_11864.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___173_11864.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___173_11864.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___173_11864.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___173_11864.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___173_11864.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___173_11864.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____11861 wl
                 | (FStar_Syntax_Syntax.Comp _,FStar_Syntax_Syntax.GTotal _)
                   |(FStar_Syntax_Syntax.Comp _,FStar_Syntax_Syntax.Total _)
                     ->
                     let uu____11873 =
                       let uu___174_11876 = problem  in
                       let uu____11879 =
                         let uu____11880 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____11880
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___174_11876.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___174_11876.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___174_11876.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____11879;
                         FStar_TypeChecker_Common.element =
                           (uu___174_11876.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___174_11876.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___174_11876.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___174_11876.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___174_11876.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___174_11876.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____11873 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____11881,FStar_Syntax_Syntax.Comp uu____11882) ->
                     let uu____11883 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21)))
                        in
                     if uu____11883
                     then
                       let uu____11884 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type"
                          in
                       solve_t env uu____11884 wl
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
                           (let uu____11894 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____11894
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____11896 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____11896 with
                            | None  ->
                                let uu____11898 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____11899 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ
                                        in
                                     FStar_Syntax_Util.non_informative
                                       uu____11899)
                                   in
                                if uu____11898
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
                                  (let uu____11902 =
                                     let uu____11903 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name
                                        in
                                     let uu____11904 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name
                                        in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____11903 uu____11904
                                      in
                                   giveup env uu____11902 orig)
                            | Some edge -> solve_sub c12 edge c22))))))

let print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____11909 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____11929  ->
              match uu____11929 with
              | (uu____11940,uu____11941,u,uu____11943,uu____11944,uu____11945)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____11909 (FStar_String.concat ", ")
  
let ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____11974 =
        FStar_All.pipe_right (Prims.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____11974 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____11984 =
        FStar_All.pipe_right (Prims.snd ineqs)
          (FStar_List.map
             (fun uu____11996  ->
                match uu____11996 with
                | (u1,u2) ->
                    let uu____12001 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____12002 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____12001 uu____12002))
         in
      FStar_All.pipe_right uu____11984 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____12014,[])) -> "{}"
      | uu____12027 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____12037 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____12037
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____12040 =
              FStar_List.map
                (fun uu____12044  ->
                   match uu____12044 with
                   | (uu____12047,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____12040 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____12051 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____12051 imps
  
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____12089 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel")
       in
    if uu____12089
    then
      let uu____12090 = FStar_TypeChecker_Normalize.term_to_string env lhs
         in
      let uu____12091 = FStar_TypeChecker_Normalize.term_to_string env rhs
         in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____12090
        (rel_to_string rel) uu____12091
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
            let uu____12111 =
              let uu____12113 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left (fun _0_71  -> Some _0_71) uu____12113  in
            FStar_Syntax_Syntax.new_bv uu____12111 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____12119 =
              let uu____12121 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left (fun _0_72  -> Some _0_72) uu____12121  in
            let uu____12123 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____12119 uu____12123  in
          ((FStar_TypeChecker_Common.TProb p), x)
  
let solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob * Prims.string) ->
         FStar_TypeChecker_Common.deferred Prims.option)
        -> FStar_TypeChecker_Common.deferred Prims.option
  =
  fun env  ->
    fun probs  ->
      fun err  ->
        let probs1 =
          let uu____12146 = FStar_Options.eager_inference ()  in
          if uu____12146
          then
            let uu___175_12147 = probs  in
            {
              attempting = (uu___175_12147.attempting);
              wl_deferred = (uu___175_12147.wl_deferred);
              ctr = (uu___175_12147.ctr);
              defer_ok = false;
              smt_ok = (uu___175_12147.smt_ok);
              tcenv = (uu___175_12147.tcenv)
            }
          else probs  in
        let tx = FStar_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred -> (FStar_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Unionfind.rollback tx;
             (let uu____12158 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____12158
              then
                let uu____12159 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____12159
              else ());
             err (d, s))
  
let simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____12169 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____12169
            then
              let uu____12170 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____12170
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f
               in
            (let uu____12174 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____12174
             then
               let uu____12175 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____12175
             else ());
            (let f2 =
               let uu____12178 =
                 let uu____12179 = FStar_Syntax_Util.unmeta f1  in
                 uu____12179.FStar_Syntax_Syntax.n  in
               match uu____12178 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____12183 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___176_12184 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___176_12184.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___176_12184.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___176_12184.FStar_TypeChecker_Env.implicits)
             })))
  
let with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_TypeChecker_Common.deferred Prims.option ->
        FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | None  -> None
        | Some d ->
            let uu____12199 =
              let uu____12200 =
                let uu____12201 =
                  let uu____12202 =
                    FStar_All.pipe_right (p_guard prob) Prims.fst  in
                  FStar_All.pipe_right uu____12202
                    (fun _0_73  -> FStar_TypeChecker_Common.NonTrivial _0_73)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____12201;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____12200  in
            FStar_All.pipe_left (fun _0_74  -> Some _0_74) uu____12199
  
let try_teq :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____12229 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____12229
           then
             let uu____12230 = FStar_Syntax_Print.term_to_string t1  in
             let uu____12231 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____12230
               uu____12231
           else ());
          (let prob =
             let uu____12234 =
               let uu____12237 = FStar_TypeChecker_Env.get_range env  in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____12237
                in
             FStar_All.pipe_left
               (fun _0_75  -> FStar_TypeChecker_Common.TProb _0_75)
               uu____12234
              in
           let g =
             let uu____12242 =
               let uu____12244 = singleton' env prob smt_ok  in
               solve_and_commit env uu____12244 (fun uu____12245  -> None)
                in
             FStar_All.pipe_left (with_guard env prob) uu____12242  in
           g)
  
let teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____12259 = try_teq true env t1 t2  in
        match uu____12259 with
        | None  ->
            let uu____12261 =
              let uu____12262 =
                let uu____12265 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1  in
                let uu____12266 = FStar_TypeChecker_Env.get_range env  in
                (uu____12265, uu____12266)  in
              FStar_Errors.Error uu____12262  in
            Prims.raise uu____12261
        | Some g ->
            ((let uu____12269 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12269
              then
                let uu____12270 = FStar_Syntax_Print.term_to_string t1  in
                let uu____12271 = FStar_Syntax_Print.term_to_string t2  in
                let uu____12272 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____12270
                  uu____12271 uu____12272
              else ());
             g)
  
let try_subtype' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        Prims.bool -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        fun smt_ok  ->
          (let uu____12288 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____12288
           then
             let uu____12289 =
               FStar_TypeChecker_Normalize.term_to_string env t1  in
             let uu____12290 =
               FStar_TypeChecker_Normalize.term_to_string env t2  in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____12289
               uu____12290
           else ());
          (let uu____12292 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2  in
           match uu____12292 with
           | (prob,x) ->
               let g =
                 let uu____12300 =
                   let uu____12302 = singleton' env prob smt_ok  in
                   solve_and_commit env uu____12302
                     (fun uu____12303  -> None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____12300  in
               ((let uu____12309 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g)
                    in
                 if uu____12309
                 then
                   let uu____12310 =
                     FStar_TypeChecker_Normalize.term_to_string env t1  in
                   let uu____12311 =
                     FStar_TypeChecker_Normalize.term_to_string env t2  in
                   let uu____12312 =
                     let uu____12313 = FStar_Util.must g  in
                     guard_to_string env uu____12313  in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____12310 uu____12311 uu____12312
                 else ());
                abstract_guard x g))
  
let try_subtype :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t Prims.option
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
          let uu____12337 = FStar_TypeChecker_Env.get_range env  in
          let uu____12338 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1  in
          FStar_Errors.report uu____12337 uu____12338
  
let sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____12350 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____12350
         then
           let uu____12351 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____12352 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____12351
             uu____12352
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB  in
         let prob =
           let uu____12357 =
             let uu____12360 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 None uu____12360 "sub_comp"  in
           FStar_All.pipe_left
             (fun _0_76  -> FStar_TypeChecker_Common.CProb _0_76) uu____12357
            in
         let uu____12363 =
           let uu____12365 = singleton env prob  in
           solve_and_commit env uu____12365 (fun uu____12366  -> None)  in
         FStar_All.pipe_left (with_guard env prob) uu____12363)
  
let solve_universe_inequalities' :
  FStar_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list *
        (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____12385  ->
        match uu____12385 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Unionfind.rollback tx;
              (let uu____12410 =
                 let uu____12411 =
                   let uu____12414 =
                     let uu____12415 = FStar_Syntax_Print.univ_to_string u1
                        in
                     let uu____12416 = FStar_Syntax_Print.univ_to_string u2
                        in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____12415 uu____12416
                      in
                   let uu____12417 = FStar_TypeChecker_Env.get_range env  in
                   (uu____12414, uu____12417)  in
                 FStar_Errors.Error uu____12411  in
               Prims.raise uu____12410)
               in
            let equiv v1 v' =
              let uu____12425 =
                let uu____12428 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____12429 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____12428, uu____12429)  in
              match uu____12425 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Unionfind.equivalent v0 v0'
              | uu____12437 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____12451 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____12451 with
                      | FStar_Syntax_Syntax.U_unif uu____12455 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____12466  ->
                                    match uu____12466 with
                                    | (u,v') ->
                                        let uu____12472 = equiv v1 v'  in
                                        if uu____12472
                                        then
                                          let uu____12474 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u))
                                             in
                                          (if uu____12474 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____12484 -> []))
               in
            let uu____12487 =
              let wl =
                let uu___177_12490 = empty_worklist env  in
                {
                  attempting = (uu___177_12490.attempting);
                  wl_deferred = (uu___177_12490.wl_deferred);
                  ctr = (uu___177_12490.ctr);
                  defer_ok = false;
                  smt_ok = (uu___177_12490.smt_ok);
                  tcenv = (uu___177_12490.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____12497  ->
                      match uu____12497 with
                      | (lb,v1) ->
                          let uu____12502 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____12502 with
                           | USolved wl1 -> ()
                           | uu____12504 -> fail lb v1)))
               in
            let rec check_ineq uu____12510 =
              match uu____12510 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____12517) -> true
                   | (FStar_Syntax_Syntax.U_succ
                      u0,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name
                      u0,FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif
                      u0,FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Unionfind.equivalent u0 v0
                   | (FStar_Syntax_Syntax.U_name _,FStar_Syntax_Syntax.U_succ
                      v0)
                     |(FStar_Syntax_Syntax.U_unif
                       _,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____12533) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____12537,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____12542 -> false)
               in
            let uu____12545 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____12551  ->
                      match uu____12551 with
                      | (u,v1) ->
                          let uu____12556 = check_ineq (u, v1)  in
                          if uu____12556
                          then true
                          else
                            ((let uu____12559 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____12559
                              then
                                let uu____12560 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____12561 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____12560
                                  uu____12561
                              else ());
                             false)))
               in
            if uu____12545
            then ()
            else
              ((let uu____12565 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____12565
                then
                  ((let uu____12567 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____12567);
                   FStar_Unionfind.rollback tx;
                   (let uu____12573 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____12573))
                else ());
               (let uu____12579 =
                  let uu____12580 =
                    let uu____12583 = FStar_TypeChecker_Env.get_range env  in
                    ("Failed to solve universe inequalities for inductives",
                      uu____12583)
                     in
                  FStar_Errors.Error uu____12580  in
                Prims.raise uu____12579))
  
let solve_universe_inequalities :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe
      * FStar_Syntax_Syntax.universe) Prims.list) -> Prims.unit
  =
  fun env  ->
    fun ineqs  ->
      let tx = FStar_Unionfind.new_transaction ()  in
      solve_universe_inequalities' tx env ineqs; FStar_Unionfind.commit tx
  
let rec solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let fail uu____12616 =
        match uu____12616 with
        | (d,s) ->
            let msg = explain env d s  in
            Prims.raise (FStar_Errors.Error (msg, (p_loc d)))
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____12626 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____12626
       then
         let uu____12627 = wl_to_string wl  in
         let uu____12628 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits)
            in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____12627 uu____12628
       else ());
      (let g1 =
         let uu____12640 = solve_and_commit env wl fail  in
         match uu____12640 with
         | Some [] ->
             let uu___178_12647 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___178_12647.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___178_12647.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___178_12647.FStar_TypeChecker_Env.implicits)
             }
         | uu____12650 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___179_12653 = g1  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___179_12653.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___179_12653.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___179_12653.FStar_TypeChecker_Env.implicits)
        }))
  
let discharge_guard' :
  (Prims.unit -> Prims.string) Prims.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t ->
        Prims.bool -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun use_env_range_msg  ->
    fun env  ->
      fun g  ->
        fun use_smt  ->
          let g1 = solve_deferred_constraints env g  in
          let ret_g =
            let uu___180_12679 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___180_12679.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___180_12679.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___180_12679.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____12680 =
            let uu____12681 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____12681  in
          if uu____12680
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____12687 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Norm")
                      in
                   if uu____12687
                   then
                     let uu____12688 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____12689 =
                       let uu____12690 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____12690
                        in
                     FStar_Errors.diag uu____12688 uu____12689
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Simplify] env vc
                      in
                   match check_trivial vc1 with
                   | FStar_TypeChecker_Common.Trivial  -> Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then None
                       else
                         ((let uu____12699 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____12699
                           then
                             let uu____12700 =
                               FStar_TypeChecker_Env.get_range env  in
                             let uu____12701 =
                               let uu____12702 =
                                 FStar_Syntax_Print.term_to_string vc2  in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____12702
                                in
                             FStar_Errors.diag uu____12700 uu____12701
                           else ());
                          (let vcs =
                             let uu____12708 = FStar_Options.use_tactics ()
                                in
                             if uu____12708
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)]  in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____12722  ->
                                   match uu____12722 with
                                   | (env1,goal) ->
                                       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                         use_env_range_msg env1 goal)));
                          Some ret_g))))
  
let discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____12733 = discharge_guard' None env g true  in
      match uu____12733 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let resolve_implicits :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____12753 = FStar_Unionfind.find u  in
      match uu____12753 with
      | FStar_Syntax_Syntax.Uvar  -> true
      | uu____12762 -> false  in
    let rec until_fixpoint acc implicits =
      let uu____12777 = acc  in
      match uu____12777 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____12823 = hd1  in
               (match uu____12823 with
                | (uu____12830,env,u,tm,k,r) ->
                    let uu____12836 = unresolved u  in
                    if uu____12836
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k  in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm
                          in
                       (let uu____12854 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck")
                           in
                        if uu____12854
                        then
                          let uu____12855 =
                            FStar_Syntax_Print.uvar_to_string u  in
                          let uu____12859 =
                            FStar_Syntax_Print.term_to_string tm1  in
                          let uu____12860 =
                            FStar_Syntax_Print.term_to_string k  in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____12855 uu____12859 uu____12860
                        else ());
                       (let uu____12862 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___181_12866 = env1  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___181_12866.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___181_12866.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___181_12866.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___181_12866.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___181_12866.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___181_12866.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___181_12866.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___181_12866.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___181_12866.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___181_12866.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___181_12866.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___181_12866.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___181_12866.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___181_12866.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___181_12866.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___181_12866.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___181_12866.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___181_12866.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___181_12866.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___181_12866.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___181_12866.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___181_12866.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___181_12866.FStar_TypeChecker_Env.qname_and_index)
                             }) tm1
                           in
                        match uu____12862 with
                        | (uu____12867,uu____12868,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___182_12871 = g1  in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___182_12871.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___182_12871.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___182_12871.FStar_TypeChecker_Env.implicits)
                                }
                              else g1  in
                            let g' =
                              let uu____12874 =
                                discharge_guard'
                                  (Some
                                     (fun uu____12878  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true
                                 in
                              match uu____12874 with
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
    let uu___183_12893 = g  in
    let uu____12894 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___183_12893.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___183_12893.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___183_12893.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____12894
    }
  
let force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____12922 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____12922 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____12929 = discharge_guard env g1  in
          FStar_All.pipe_left Prims.ignore uu____12929
      | (reason,uu____12931,uu____12932,e,t,r)::uu____12936 ->
          let uu____12950 =
            let uu____12951 = FStar_Syntax_Print.term_to_string t  in
            let uu____12952 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format3
              "Failed to resolve implicit argument of type '%s' introduced in %s because %s"
              uu____12951 uu____12952 reason
             in
          FStar_Errors.report r uu____12950
  
let universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___184_12959 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___184_12959.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___184_12959.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___184_12959.FStar_TypeChecker_Env.implicits)
      }
  
let teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____12977 = try_teq false env t1 t2  in
        match uu____12977 with
        | None  -> false
        | Some g ->
            let uu____12980 = discharge_guard' None env g false  in
            (match uu____12980 with
             | Some uu____12984 -> true
             | None  -> false)
  