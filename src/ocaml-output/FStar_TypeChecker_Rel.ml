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
    FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun x  ->
    fun g  ->
      match g with
      | FStar_Pervasives_Native.None  -> g
      | FStar_Pervasives_Native.Some
          {
            FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
            FStar_TypeChecker_Env.deferred = uu____56;
            FStar_TypeChecker_Env.univ_ineqs = uu____57;
            FStar_TypeChecker_Env.implicits = uu____58;_}
          -> g
      | FStar_Pervasives_Native.Some g1 ->
          let f =
            match g1.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.NonTrivial f -> f
            | uu____73 -> failwith "impossible"  in
          let uu____74 =
            let uu___133_75 = g1  in
            let uu____76 =
              let uu____77 =
                let uu____78 =
                  let uu____79 = FStar_Syntax_Syntax.mk_binder x  in
                  [uu____79]  in
                let uu____80 =
                  let uu____87 =
                    let uu____93 =
                      let uu____94 =
                        FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                         in
                      FStar_All.pipe_right uu____94
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    FStar_All.pipe_right uu____93
                      (fun _0_29  -> FStar_Util.Inl _0_29)
                     in
                  FStar_Pervasives_Native.Some uu____87  in
                FStar_Syntax_Util.abs uu____78 f uu____80  in
              FStar_All.pipe_left
                (fun _0_30  -> FStar_TypeChecker_Common.NonTrivial _0_30)
                uu____77
               in
            {
              FStar_TypeChecker_Env.guard_f = uu____76;
              FStar_TypeChecker_Env.deferred =
                (uu___133_75.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___133_75.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___133_75.FStar_TypeChecker_Env.implicits)
            }  in
          FStar_Pervasives_Native.Some uu____74
  
let apply_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___134_115 = g  in
          let uu____116 =
            let uu____117 =
              let uu____118 =
                let uu____121 =
                  let uu____122 =
                    let uu____132 =
                      let uu____134 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____134]  in
                    (f, uu____132)  in
                  FStar_Syntax_Syntax.Tm_app uu____122  in
                FStar_Syntax_Syntax.mk uu____121  in
              uu____118
                (FStar_Pervasives_Native.Some
                   (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_31  -> FStar_TypeChecker_Common.NonTrivial _0_31)
              uu____117
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____116;
            FStar_TypeChecker_Env.deferred =
              (uu___134_115.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___134_115.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___134_115.FStar_TypeChecker_Env.implicits)
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
          let uu___135_156 = g  in
          let uu____157 =
            let uu____158 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____158  in
          {
            FStar_TypeChecker_Env.guard_f = uu____157;
            FStar_TypeChecker_Env.deferred =
              (uu___135_156.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___135_156.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___135_156.FStar_TypeChecker_Env.implicits)
          }
  
let trivial : FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____162 -> failwith "impossible"
  
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
          let uu____173 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____173
  
let check_trivial :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_TypeChecker_Common.guard_formula
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____182 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____213 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____213;
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
                       let uu____258 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____258
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___136_260 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___136_260.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___136_260.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___136_260.FStar_TypeChecker_Env.implicits)
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
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  FStar_Syntax_Util.mk_forall u
                    (FStar_Pervasives_Native.fst b) f1)) bs f
  
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
            let uu___137_287 = g  in
            let uu____288 =
              let uu____289 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____289  in
            {
              FStar_TypeChecker_Env.guard_f = uu____288;
              FStar_TypeChecker_Env.deferred =
                (uu___137_287.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___137_287.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___137_287.FStar_TypeChecker_Env.implicits)
            }
  
let new_uvar :
  FStar_Range.range ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun binders  ->
      fun k  ->
        let uv = FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar  in
        match binders with
        | [] ->
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k))
                (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.n)) r
               in
            (uv1, uv1)
        | uu____330 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder)
               in
            let k' =
              let uu____345 = FStar_Syntax_Syntax.mk_Total k  in
              FStar_Syntax_Util.arrow binders uu____345  in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                FStar_Pervasives_Native.None r
               in
            let uu____361 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.n)) r
               in
            (uu____361, uv1)
  
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
  | TERM of
  ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2 
let uu___is_TERM : uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____423 -> false
  
let __proj__TERM__item___0 :
  uvi ->
    ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
       FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let uu___is_UNIV : uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____449 -> false
  
let __proj__UNIV__item___0 :
  uvi ->
    (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2
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
  tcenv: FStar_TypeChecker_Env.env }
type solution =
  | Success of FStar_TypeChecker_Common.deferred 
  | Failed of (FStar_TypeChecker_Common.prob,Prims.string)
  FStar_Pervasives_Native.tuple2 
let uu___is_Success : solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____537 -> false
  
let __proj__Success__item___0 : solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0 
let uu___is_Failed : solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____551 -> false
  
let __proj__Failed__item___0 :
  solution ->
    (FStar_TypeChecker_Common.prob,Prims.string)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let uu___is_COVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____568 -> false
  
let uu___is_CONTRAVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____572 -> false
  
let uu___is_INVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____576 -> false
  
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___105_591  ->
    match uu___105_591 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let term_to_string env t =
  let uu____604 =
    let uu____605 = FStar_Syntax_Subst.compress t  in
    uu____605.FStar_Syntax_Syntax.n  in
  match uu____604 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____622 = FStar_Syntax_Print.uvar_to_string u  in
      let uu____626 = FStar_Syntax_Print.term_to_string t1  in
      FStar_Util.format2 "(%s:%s)" uu____622 uu____626
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____629;
         FStar_Syntax_Syntax.pos = uu____630;
         FStar_Syntax_Syntax.vars = uu____631;_},args)
      ->
      let uu____659 = FStar_Syntax_Print.uvar_to_string u  in
      let uu____663 = FStar_Syntax_Print.term_to_string ty  in
      let uu____664 = FStar_Syntax_Print.args_to_string args  in
      FStar_Util.format3 "(%s:%s) %s" uu____659 uu____663 uu____664
  | uu____665 -> FStar_Syntax_Print.term_to_string t 
let prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___106_671  ->
      match uu___106_671 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____675 =
            let uu____677 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____678 =
              let uu____680 =
                term_to_string env p.FStar_TypeChecker_Common.lhs  in
              let uu____681 =
                let uu____683 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs
                   in
                let uu____684 =
                  let uu____686 =
                    let uu____688 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs  in
                    let uu____689 =
                      let uu____691 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs
                         in
                      let uu____692 =
                        let uu____694 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (FStar_Pervasives_Native.fst
                               p.FStar_TypeChecker_Common.logical_guard)
                           in
                        let uu____695 =
                          let uu____697 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t")
                             in
                          [uu____697]  in
                        uu____694 :: uu____695  in
                      uu____691 :: uu____692  in
                    uu____688 :: uu____689  in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____686
                   in
                uu____683 :: uu____684  in
              uu____680 :: uu____681  in
            uu____677 :: uu____678  in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____675
      | FStar_TypeChecker_Common.CProb p ->
          let uu____702 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____703 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____702
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____703
  
let uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___107_709  ->
      match uu___107_709 with
      | UNIV (u,t) ->
          let x =
            let uu____713 = FStar_Options.hide_uvar_nums ()  in
            if uu____713
            then "?"
            else
              (let uu____715 = FStar_Unionfind.uvar_id u  in
               FStar_All.pipe_right uu____715 FStar_Util.string_of_int)
             in
          let uu____717 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____717
      | TERM ((u,uu____719),t) ->
          let x =
            let uu____724 = FStar_Options.hide_uvar_nums ()  in
            if uu____724
            then "?"
            else
              (let uu____726 = FStar_Unionfind.uvar_id u  in
               FStar_All.pipe_right uu____726 FStar_Util.string_of_int)
             in
          let uu____730 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____730
  
let uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____739 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____739 (FStar_String.concat ", ")
  
let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____747 =
      let uu____749 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____749
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____747 (FStar_String.concat ", ")
  
let args_to_string args =
  let uu____767 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____775  ->
            match uu____775 with
            | (x,uu____779) -> FStar_Syntax_Print.term_to_string x))
     in
  FStar_All.pipe_right uu____767 (FStar_String.concat " ") 
let empty_worklist : FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____784 =
      let uu____785 = FStar_Options.eager_inference ()  in
      Prims.op_Negation uu____785  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____784;
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
        let uu___138_798 = empty_worklist env  in
        {
          attempting = [prob];
          wl_deferred = (uu___138_798.wl_deferred);
          ctr = (uu___138_798.ctr);
          defer_ok = (uu___138_798.defer_ok);
          smt_ok;
          tcenv = (uu___138_798.tcenv)
        }
  
let singleton :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true 
let wl_of_guard env g =
  let uu___139_823 = empty_worklist env  in
  let uu____824 = FStar_List.map FStar_Pervasives_Native.snd g  in
  {
    attempting = uu____824;
    wl_deferred = (uu___139_823.wl_deferred);
    ctr = (uu___139_823.ctr);
    defer_ok = false;
    smt_ok = (uu___139_823.smt_ok);
    tcenv = (uu___139_823.tcenv)
  } 
let defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___140_836 = wl  in
        {
          attempting = (uu___140_836.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___140_836.ctr);
          defer_ok = (uu___140_836.defer_ok);
          smt_ok = (uu___140_836.smt_ok);
          tcenv = (uu___140_836.tcenv)
        }
  
let attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist =
  fun probs  ->
    fun wl  ->
      let uu___141_848 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___141_848.wl_deferred);
        ctr = (uu___141_848.ctr);
        defer_ok = (uu___141_848.defer_ok);
        smt_ok = (uu___141_848.smt_ok);
        tcenv = (uu___141_848.tcenv)
      }
  
let giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____859 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____859
         then
           let uu____860 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____860
         else ());
        Failed (prob, reason)
  
let invert_rel : FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___108_864  ->
    match uu___108_864 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert p =
  let uu___142_880 = p  in
  {
    FStar_TypeChecker_Common.pid =
      (uu___142_880.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___142_880.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___142_880.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___142_880.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___142_880.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___142_880.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___142_880.FStar_TypeChecker_Common.rank)
  } 
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p 
let maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___109_901  ->
    match uu___109_901 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_32  -> FStar_TypeChecker_Common.TProb _0_32)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_33  -> FStar_TypeChecker_Common.CProb _0_33)
  
let vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___110_917  ->
      match uu___110_917 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let p_pid : FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___111_920  ->
    match uu___111_920 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___112_929  ->
    match uu___112_929 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___113_939  ->
    match uu___113_939 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___114_949  ->
    match uu___114_949 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let p_guard :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___115_960  ->
    match uu___115_960 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let p_scope : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___116_971  ->
    match uu___116_971 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
  
let p_invert : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___117_980  ->
    match uu___117_980 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_34  -> FStar_TypeChecker_Common.TProb _0_34) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_35  -> FStar_TypeChecker_Common.CProb _0_35) (invert p)
  
let is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____994 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____994 = (Prims.parse_int "1")
  
let next_pid : Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1005  -> FStar_Util.incr ctr; FStar_ST.read ctr 
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1055 = next_pid ()  in
  let uu____1056 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0  in
  {
    FStar_TypeChecker_Common.pid = uu____1055;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1056;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
  } 
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env  in
  let uu____1103 = next_pid ()  in
  let uu____1104 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0  in
  {
    FStar_TypeChecker_Common.pid = uu____1103;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1104;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
  } 
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1145 = next_pid ()  in
  {
    FStar_TypeChecker_Common.pid = uu____1145;
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
let guard_on_element wl problem x phi =
  match problem.FStar_TypeChecker_Common.element with
  | FStar_Pervasives_Native.None  ->
      let u =
        (wl.tcenv).FStar_TypeChecker_Env.universe_of wl.tcenv
          x.FStar_Syntax_Syntax.sort
         in
      FStar_Syntax_Util.mk_forall u x phi
  | FStar_Pervasives_Native.Some e ->
      FStar_Syntax_Subst.subst [FStar_Syntax_Syntax.NT (x, e)] phi
  
let explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____1197 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel")
           in
        if uu____1197
        then
          let uu____1198 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____1199 = prob_to_string env d  in
          let uu____1200 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1198 uu____1199 uu____1200 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1205 -> failwith "impossible"  in
           let uu____1206 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1214 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____1215 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____1214, uu____1215)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1219 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____1220 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____1219, uu____1220)
              in
           match uu____1206 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let commit : uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___118_1229  ->
            match uu___118_1229 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Unionfind.union u u'
                 | uu____1236 ->
                     FStar_Unionfind.change u
                       (FStar_Pervasives_Native.Some t))
            | TERM ((u,uu____1239),t) -> FStar_Syntax_Util.set_uvar u t))
  
let find_term_uvar :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
    FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___119_1262  ->
           match uu___119_1262 with
           | UNIV uu____1264 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1268),t) ->
               let uu____1272 = FStar_Unionfind.equivalent uv u  in
               if uu____1272
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None)
  
let find_univ_uvar :
  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.uvar ->
    uvi Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___120_1291  ->
           match uu___120_1291 with
           | UNIV (u',t) ->
               let uu____1295 = FStar_Unionfind.equivalent u u'  in
               if uu____1295
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1299 -> FStar_Pervasives_Native.None)
  
let whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1306 =
        let uu____1307 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1307
         in
      FStar_Syntax_Subst.compress uu____1306
  
let sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1314 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____1314
  
let norm_arg env t =
  let uu____1333 = sn env (FStar_Pervasives_Native.fst t)  in
  (uu____1333, (FStar_Pervasives_Native.snd t)) 
let sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1350  ->
              match uu____1350 with
              | (x,imp) ->
                  let uu____1357 =
                    let uu___143_1358 = x  in
                    let uu____1359 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___143_1358.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___143_1358.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1359
                    }  in
                  (uu____1357, imp)))
  
let norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1374 = aux u3  in FStar_Syntax_Syntax.U_succ uu____1374
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1377 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____1377
        | uu____1379 -> u2  in
      let uu____1380 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1380
  
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0 
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then
          ((x.FStar_Syntax_Syntax.sort),
            (FStar_Pervasives_Native.Some (x, phi)))
        else
          (let uu____1487 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           match uu____1487 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1499;
               FStar_Syntax_Syntax.pos = uu____1500;
               FStar_Syntax_Syntax.vars = uu____1501;_} ->
               ((x1.FStar_Syntax_Syntax.sort),
                 (FStar_Pervasives_Native.Some (x1, phi1)))
           | tt ->
               let uu____1522 =
                 let uu____1523 = FStar_Syntax_Print.term_to_string tt  in
                 let uu____1524 = FStar_Syntax_Print.tag_of_term tt  in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1523
                   uu____1524
                  in
               failwith uu____1522)
    | FStar_Syntax_Syntax.Tm_uinst uu____1534 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           let uu____1561 =
             let uu____1562 = FStar_Syntax_Subst.compress t1'  in
             uu____1562.FStar_Syntax_Syntax.n  in
           match uu____1561 with
           | FStar_Syntax_Syntax.Tm_refine uu____1574 -> aux true t1'
           | uu____1579 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_fvar uu____1591 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           let uu____1614 =
             let uu____1615 = FStar_Syntax_Subst.compress t1'  in
             uu____1615.FStar_Syntax_Syntax.n  in
           match uu____1614 with
           | FStar_Syntax_Syntax.Tm_refine uu____1627 -> aux true t1'
           | uu____1632 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_app uu____1644 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           let uu____1676 =
             let uu____1677 = FStar_Syntax_Subst.compress t1'  in
             uu____1677.FStar_Syntax_Syntax.n  in
           match uu____1676 with
           | FStar_Syntax_Syntax.Tm_refine uu____1689 -> aux true t1'
           | uu____1694 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_type uu____1706 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_constant uu____1718 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_name uu____1730 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_bvar uu____1742 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_arrow uu____1754 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_abs uu____1773 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_uvar uu____1799 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_let uu____1819 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_match uu____1838 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_meta uu____1865 ->
        let uu____1870 =
          let uu____1871 = FStar_Syntax_Print.term_to_string t11  in
          let uu____1872 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1871
            uu____1872
           in
        failwith uu____1870
    | FStar_Syntax_Syntax.Tm_ascribed uu____1882 ->
        let uu____1900 =
          let uu____1901 = FStar_Syntax_Print.term_to_string t11  in
          let uu____1902 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1901
            uu____1902
           in
        failwith uu____1900
    | FStar_Syntax_Syntax.Tm_delayed uu____1912 ->
        let uu____1933 =
          let uu____1934 = FStar_Syntax_Print.term_to_string t11  in
          let uu____1935 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1934
            uu____1935
           in
        failwith uu____1933
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____1945 =
          let uu____1946 = FStar_Syntax_Print.term_to_string t11  in
          let uu____1947 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1946
            uu____1947
           in
        failwith uu____1945
     in
  let uu____1957 = whnf env t1  in aux false uu____1957 
let unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1966 =
        let uu____1976 = empty_worklist env  in
        base_and_refinement env uu____1976 t  in
      FStar_All.pipe_right uu____1966 FStar_Pervasives_Native.fst
  
let trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____2000 = FStar_Syntax_Syntax.null_bv t  in
    (uu____2000, FStar_Syntax_Util.t_true)
  
let as_refinement env wl t =
  let uu____2020 = base_and_refinement env wl t  in
  match uu____2020 with
  | (t_base,refinement) ->
      (match refinement with
       | FStar_Pervasives_Native.None  -> trivial_refinement t_base
       | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let force_refinement uu____2079 =
  match uu____2079 with
  | (t_base,refopt) ->
      let uu____2093 =
        match refopt with
        | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
        | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
      (match uu____2093 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___121_2117  ->
      match uu___121_2117 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2121 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____2122 =
            let uu____2123 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
            FStar_Syntax_Print.term_to_string uu____2123  in
          let uu____2124 =
            let uu____2125 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
            FStar_Syntax_Print.term_to_string uu____2125  in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2121 uu____2122
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2124
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2129 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____2130 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____2131 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2129 uu____2130
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2131
  
let wl_to_string : worklist -> Prims.string =
  fun wl  ->
    let uu____2135 =
      let uu____2137 =
        let uu____2139 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2149  ->
                  match uu____2149 with | (uu____2153,uu____2154,x) -> x))
           in
        FStar_List.append wl.attempting uu____2139  in
      FStar_List.map (wl_prob_to_string wl) uu____2137  in
    FStar_All.pipe_right uu____2135 (FStar_String.concat "\n\t")
  
let u_abs :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2172 =
          let uu____2182 =
            let uu____2183 = FStar_Syntax_Subst.compress k  in
            uu____2183.FStar_Syntax_Syntax.n  in
          match uu____2182 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2224 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____2224)
              else
                (let uu____2238 = FStar_Syntax_Util.abs_formals t  in
                 match uu____2238 with
                 | (ys',t1,uu____2259) ->
                     let uu____2272 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____2272))
          | uu____2293 ->
              let uu____2294 =
                let uu____2300 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____2300)  in
              ((ys, t), uu____2294)
           in
        match uu____2172 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (FStar_Pervasives_Native.Some
                   (FStar_Util.Inr (FStar_Parser_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____2355 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____2355 c  in
               let uu____2357 =
                 let uu____2364 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_36  -> FStar_Util.Inl _0_36)
                    in
                 FStar_All.pipe_right uu____2364
                   (fun _0_37  -> FStar_Pervasives_Native.Some _0_37)
                  in
               FStar_Syntax_Util.abs ys1 t1 uu____2357)
  
let solve_prob' :
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
              | FStar_Pervasives_Native.Some phi -> phi  in
            let uu____2415 = p_guard prob  in
            match uu____2415 with
            | (uu____2418,uv) ->
                ((let uu____2421 =
                    let uu____2422 = FStar_Syntax_Subst.compress uv  in
                    uu____2422.FStar_Syntax_Syntax.n  in
                  match uu____2421 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob  in
                      let phi1 = u_abs k bs phi  in
                      ((let uu____2442 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel")
                           in
                        if uu____2442
                        then
                          let uu____2443 =
                            FStar_Util.string_of_int (p_pid prob)  in
                          let uu____2444 =
                            FStar_Syntax_Print.term_to_string uv  in
                          let uu____2445 =
                            FStar_Syntax_Print.term_to_string phi1  in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2443
                            uu____2444 uu____2445
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2449 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___144_2452 = wl  in
                  {
                    attempting = (uu___144_2452.attempting);
                    wl_deferred = (uu___144_2452.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___144_2452.defer_ok);
                    smt_ok = (uu___144_2452.smt_ok);
                    tcenv = (uu___144_2452.tcenv)
                  }))
  
let extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2465 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck")
            in
         if uu____2465
         then
           let uu____2466 = FStar_Util.string_of_int pid  in
           let uu____2467 =
             let uu____2468 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____2468 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2466 uu____2467
         else ());
        commit sol;
        (let uu___145_2473 = wl  in
         {
           attempting = (uu___145_2473.attempting);
           wl_deferred = (uu___145_2473.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___145_2473.defer_ok);
           smt_ok = (uu___145_2473.smt_ok);
           tcenv = (uu___145_2473.tcenv)
         })
  
let solve_prob :
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
            | (uu____2502,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2510 = FStar_Syntax_Util.mk_conj t1 f  in
                FStar_Pervasives_Native.Some uu____2510
             in
          (let uu____2516 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck")
              in
           if uu____2516
           then
             let uu____2517 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____2518 =
               let uu____2519 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____2519 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2517 uu____2518
           else ());
          solve_prob' false prob logical_guard uvis wl
  
let rec occurs wl uk t =
  let uu____2544 =
    let uu____2548 = FStar_Syntax_Free.uvars t  in
    FStar_All.pipe_right uu____2548 FStar_Util.set_elements  in
  FStar_All.pipe_right uu____2544
    (FStar_Util.for_some
       (fun uu____2569  ->
          match uu____2569 with
          | (uv,uu____2577) ->
              FStar_Unionfind.equivalent uv (FStar_Pervasives_Native.fst uk)))
  
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2621 = occurs wl uk t  in Prims.op_Negation uu____2621  in
  let msg =
    if occurs_ok
    then FStar_Pervasives_Native.None
    else
      (let uu____2626 =
         let uu____2627 =
           FStar_Syntax_Print.uvar_to_string (FStar_Pervasives_Native.fst uk)
            in
         let uu____2631 = FStar_Syntax_Print.term_to_string t  in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2627 uu____2631
          in
       FStar_Pervasives_Native.Some uu____2626)
     in
  (occurs_ok, msg) 
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t  in
  let uu____2679 = occurs_check env wl uk t  in
  match uu____2679 with
  | (occurs_ok,msg) ->
      let uu____2696 = FStar_Util.set_is_subset_of fvs_t fvs  in
      (occurs_ok, uu____2696, (msg, fvs, fvs_t))
  
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  ->
            fun x  -> FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
         FStar_Syntax_Syntax.no_names)
     in
  let v1_set = as_set1 v1  in
  let uu____2760 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2784  ->
            fun uu____2785  ->
              match (uu____2784, uu____2785) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2828 =
                    let uu____2829 = FStar_Util.set_mem x v1_set  in
                    FStar_All.pipe_left Prims.op_Negation uu____2829  in
                  if uu____2828
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort  in
                     let uu____2843 =
                       FStar_Util.set_is_subset_of fvs isect_set  in
                     if uu____2843
                     then
                       let uu____2850 = FStar_Util.set_add x isect_set  in
                       (((x, imp) :: isect), uu____2850)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names))
     in
  match uu____2760 with | (isect,uu____2872) -> FStar_List.rev isect 
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2921  ->
          fun uu____2922  ->
            match (uu____2921, uu____2922) with
            | ((a,uu____2932),(b,uu____2934)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg  in
  match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2978 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2984  ->
                match uu____2984 with
                | (b,uu____2988) -> FStar_Syntax_Syntax.bv_eq a b))
         in
      if uu____2978
      then FStar_Pervasives_Native.None
      else
        FStar_Pervasives_Native.Some (a, (FStar_Pervasives_Native.snd hd1))
  | uu____2997 -> FStar_Pervasives_Native.None 
let rec pat_vars :
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
            let uu____3040 = pat_var_opt env seen hd1  in
            (match uu____3040 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____3048 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel")
                      in
                   if uu____3048
                   then
                     let uu____3049 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1)
                        in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____3049
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
  
let is_flex : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3061 =
      let uu____3062 = FStar_Syntax_Subst.compress t  in
      uu____3062.FStar_Syntax_Syntax.n  in
    match uu____3061 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3065 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3074;
           FStar_Syntax_Syntax.tk = uu____3075;
           FStar_Syntax_Syntax.pos = uu____3076;
           FStar_Syntax_Syntax.vars = uu____3077;_},uu____3078)
        -> true
    | uu____3101 -> false
  
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____3163;
         FStar_Syntax_Syntax.pos = uu____3164;
         FStar_Syntax_Syntax.vars = uu____3165;_},args)
      -> (t, uv, k, args)
  | uu____3206 -> failwith "Not a flex-uvar" 
let destruct_flex_pattern env t =
  let uu____3260 = destruct_flex_t t  in
  match uu____3260 with
  | (t1,uv,k,args) ->
      let uu____3328 = pat_vars env [] args  in
      (match uu____3328 with
       | FStar_Pervasives_Native.Some vars ->
           ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
       | uu____3384 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
  
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | HeadMatch 
  | FullMatch 
let uu___is_MisMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3433 -> false
  
let __proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let uu___is_HeadMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3456 -> false
  
let uu___is_FullMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3460 -> false
  
let head_match : match_result -> match_result =
  fun uu___122_3463  ->
    match uu___122_3463 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3472 -> HeadMatch
  
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3485 ->
          let uu____3486 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____3486 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____3496 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
  
let rec delta_depth_of_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____3510 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3516 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____3538 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____3539 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____3540 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____3549 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____3557 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3574) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3580,uu____3581) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3611) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3626;
             FStar_Syntax_Syntax.index = uu____3627;
             FStar_Syntax_Syntax.sort = t2;_},uu____3629)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3636 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3637 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3638 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3646 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3662 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____3662
  
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
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____3681 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____3681
            then FullMatch
            else
              (let uu____3683 =
                 let uu____3688 =
                   let uu____3690 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____3690  in
                 let uu____3691 =
                   let uu____3693 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____3693  in
                 (uu____3688, uu____3691)  in
               MisMatch uu____3683)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3697),FStar_Syntax_Syntax.Tm_uinst (g,uu____3699)) ->
            let uu____3708 = head_matches env f g  in
            FStar_All.pipe_right uu____3708 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            if c = d
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3715),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3717)) ->
            let uu____3742 = FStar_Unionfind.equivalent uv uv'  in
            if uu____3742
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3750),FStar_Syntax_Syntax.Tm_refine (y,uu____3752)) ->
            let uu____3761 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____3761 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3763),uu____3764) ->
            let uu____3769 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____3769 head_match
        | (uu____3770,FStar_Syntax_Syntax.Tm_refine (x,uu____3772)) ->
            let uu____3777 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____3777 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____3778,FStar_Syntax_Syntax.Tm_type
           uu____3779) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____3780,FStar_Syntax_Syntax.Tm_arrow uu____3781) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3797),FStar_Syntax_Syntax.Tm_app (head',uu____3799))
            ->
            let uu____3828 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____3828 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3830),uu____3831) ->
            let uu____3846 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____3846 head_match
        | (uu____3847,FStar_Syntax_Syntax.Tm_app (head1,uu____3849)) ->
            let uu____3864 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____3864 head_match
        | uu____3865 ->
            let uu____3868 =
              let uu____3873 = delta_depth_of_term env t11  in
              let uu____3875 = delta_depth_of_term env t21  in
              (uu____3873, uu____3875)  in
            MisMatch uu____3868
  
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3911 = FStar_Syntax_Util.head_and_args t  in
    match uu____3911 with
    | (head1,uu____3923) ->
        let uu____3938 =
          let uu____3939 = FStar_Syntax_Util.un_uinst head1  in
          uu____3939.FStar_Syntax_Syntax.n  in
        (match uu____3938 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3944 =
               let uu____3945 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               FStar_All.pipe_right uu____3945 FStar_Option.isSome  in
             if uu____3944
             then
               let uu____3959 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t
                  in
               FStar_All.pipe_right uu____3959
                 (fun _0_38  -> FStar_Pervasives_Native.Some _0_38)
             else FStar_Pervasives_Native.None
         | uu____3962 -> FStar_Pervasives_Native.None)
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
        (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational
         ),uu____4030)
        ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4040 =
             let uu____4045 = maybe_inline t11  in
             let uu____4047 = maybe_inline t21  in (uu____4045, uu____4047)
              in
           match uu____4040 with
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
               fail r
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.None )
               -> aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t22)
               -> aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.Some
              t22) -> aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch
        (uu____4068,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Delta_equational ))
        ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4078 =
             let uu____4083 = maybe_inline t11  in
             let uu____4085 = maybe_inline t21  in (uu____4083, uu____4085)
              in
           match uu____4078 with
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
               fail r
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.None )
               -> aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t22)
               -> aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.Some
              t22) -> aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch
        (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some d2)
        when d1 = d2 ->
        let uu____4110 = FStar_TypeChecker_Common.decr_delta_depth d1  in
        (match uu____4110 with
         | FStar_Pervasives_Native.None  -> fail r
         | FStar_Pervasives_Native.Some d ->
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
    | MisMatch
        (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some d2) ->
        let d1_greater_than_d2 =
          FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
        let uu____4125 =
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
             let uu____4133 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21
                in
             (t11, uu____4133))
           in
        (match uu____4125 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4141 -> fail r
    | uu____4146 -> success n_delta r t11 t21  in
  aux true (Prims.parse_int "0") t1 t2 
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | C of FStar_Syntax_Syntax.comp 
let uu___is_T : tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4175 -> false 
let __proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0 
let uu___is_C : tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4205 -> false 
let __proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list
let generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4220 = FStar_Syntax_Util.type_u ()  in
      match uu____4220 with
      | (t,uu____4224) ->
          let uu____4225 = new_uvar r binders t  in
          FStar_Pervasives_Native.fst uu____4225
  
let kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4234 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____4234 FStar_Pervasives_Native.fst
  
let rec decompose :
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
      let t1 = FStar_Syntax_Util.unmeta t  in
      let matches t' =
        let uu____4276 = head_matches env t1 t'  in
        match uu____4276 with
        | MisMatch uu____4277 -> false
        | uu____4282 -> true  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4342,imp),T (t2,uu____4345)) -> (t2, imp)
                     | uu____4362 -> failwith "Bad reconstruction") args
                args'
               in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4402  ->
                    match uu____4402 with
                    | (t2,uu____4410) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____4440 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____4440 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4493))::tcs2) ->
                       aux
                         (((let uu___146_4515 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___146_4515.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___146_4515.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4525 -> failwith "Bad reconstruction"  in
                 aux [] bs1 tcs  in
               let rec decompose1 out uu___123_4556 =
                 match uu___123_4556 with
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
               let uu____4619 = decompose1 [] bs1  in
               (rebuild, matches, uu____4619))
      | uu____4647 ->
          let rebuild uu___124_4652 =
            match uu___124_4652 with
            | [] -> t1
            | uu____4654 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t2  -> true)), [])
  
let un_T : tc -> FStar_Syntax_Syntax.term =
  fun uu___125_4673  ->
    match uu___125_4673 with
    | T (t,uu____4675) -> t
    | uu____4684 -> failwith "Impossible"
  
let arg_of_tc : tc -> FStar_Syntax_Syntax.arg =
  fun uu___126_4687  ->
    match uu___126_4687 with
    | T (t,uu____4689) -> FStar_Syntax_Syntax.as_arg t
    | uu____4698 -> failwith "Impossible"
  
let imitation_sub_probs :
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
            let r = p_loc orig  in
            let rel = p_rel orig  in
            let sub_prob scope1 args q =
              match q with
              | (uu____4767,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r  in
                  let uu____4786 = new_uvar r scope1 k  in
                  (match uu____4786 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4798 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r
                          in
                       let uu____4813 =
                         let uu____4814 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm"
                            in
                         FStar_All.pipe_left
                           (fun _0_39  ->
                              FStar_TypeChecker_Common.TProb _0_39)
                           uu____4814
                          in
                       ((T (gi_xs, mk_kind)), uu____4813))
              | (uu____4823,uu____4824,C uu____4825) -> failwith "impos"  in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4912 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4923;
                         FStar_Syntax_Syntax.pos = uu____4924;
                         FStar_Syntax_Syntax.vars = uu____4925;_})
                        ->
                        let uu____4940 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____4940 with
                         | (T (gi_xs,uu____4956),prob) ->
                             let uu____4966 =
                               let uu____4967 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                               FStar_All.pipe_left (fun _0_40  -> C _0_40)
                                 uu____4967
                                in
                             (uu____4966, [prob])
                         | uu____4969 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4979;
                         FStar_Syntax_Syntax.pos = uu____4980;
                         FStar_Syntax_Syntax.vars = uu____4981;_})
                        ->
                        let uu____4996 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____4996 with
                         | (T (gi_xs,uu____5012),prob) ->
                             let uu____5022 =
                               let uu____5023 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                                  in
                               FStar_All.pipe_left (fun _0_41  -> C _0_41)
                                 uu____5023
                                in
                             (uu____5022, [prob])
                         | uu____5025 -> failwith "impossible")
                    | (uu____5031,uu____5032,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____5034;
                         FStar_Syntax_Syntax.pos = uu____5035;
                         FStar_Syntax_Syntax.vars = uu____5036;_})
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
                        let uu____5110 =
                          let uu____5115 =
                            FStar_List.map (sub_prob scope1 args) components1
                             in
                          FStar_All.pipe_right uu____5115 FStar_List.unzip
                           in
                        (match uu____5110 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5144 =
                                 let uu____5145 =
                                   let uu____5148 = FStar_List.hd tcs  in
                                   FStar_All.pipe_right uu____5148 un_T  in
                                 let uu____5149 =
                                   let uu____5155 = FStar_List.tl tcs  in
                                   FStar_All.pipe_right uu____5155
                                     (FStar_List.map arg_of_tc)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5145;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5149;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 }  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5144
                                in
                             ((C gi_xs), sub_probs))
                    | uu____5160 ->
                        let uu____5167 = sub_prob scope1 args q  in
                        (match uu____5167 with
                         | (ktec,prob) -> (ktec, [prob]))
                     in
                  (match uu____4912 with
                   | (tc,probs) ->
                       let uu____5185 =
                         match q with
                         | (FStar_Pervasives_Native.Some
                            b,uu____5211,uu____5212) ->
                             let uu____5220 =
                               let uu____5224 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b
                                  in
                               uu____5224 :: args  in
                             ((FStar_Pervasives_Native.Some b), (b ::
                               scope1), uu____5220)
                         | uu____5242 ->
                             (FStar_Pervasives_Native.None, scope1, args)
                          in
                       (match uu____5185 with
                        | (bopt,scope2,args1) ->
                            let uu____5285 = aux scope2 args1 qs2  in
                            (match uu____5285 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5306 =
                                         let uu____5308 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst))
                                            in
                                         f :: uu____5308  in
                                       FStar_Syntax_Util.mk_conj_l uu____5306
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____5321 =
                                         let uu____5323 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f
                                            in
                                         let uu____5324 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst))
                                            in
                                         uu____5323 :: uu____5324  in
                                       FStar_Syntax_Util.mk_conj_l uu____5321
                                    in
                                 ((FStar_List.append probs sub_probs), (tc ::
                                   tcs), f1))))
               in
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
let rigid_rigid : Prims.int = (Prims.parse_int "0") 
let flex_rigid_eq : Prims.int = (Prims.parse_int "1") 
let flex_refine_inner : Prims.int = (Prims.parse_int "2") 
let flex_refine : Prims.int = (Prims.parse_int "3") 
let flex_rigid : Prims.int = (Prims.parse_int "4") 
let rigid_flex : Prims.int = (Prims.parse_int "5") 
let refine_flex : Prims.int = (Prims.parse_int "6") 
let flex_flex : Prims.int = (Prims.parse_int "7") 
let compress_tprob wl p =
  let uu___147_5377 = p  in
  let uu____5380 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
  let uu____5381 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
  {
    FStar_TypeChecker_Common.pid =
      (uu___147_5377.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5380;
    FStar_TypeChecker_Common.relation =
      (uu___147_5377.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5381;
    FStar_TypeChecker_Common.element =
      (uu___147_5377.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___147_5377.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___147_5377.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___147_5377.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___147_5377.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___147_5377.FStar_TypeChecker_Common.rank)
  } 
let compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5391 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____5391
            (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
      | FStar_TypeChecker_Common.CProb uu____5396 -> p
  
let rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5410 = compress_prob wl pr  in
        FStar_All.pipe_right uu____5410 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5416 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____5416 with
           | (lh,uu____5429) ->
               let uu____5444 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____5444 with
                | (rh,uu____5457) ->
                    let uu____5472 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5481,FStar_Syntax_Syntax.Tm_uvar uu____5482)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5501,uu____5502)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5513,FStar_Syntax_Syntax.Tm_uvar uu____5514)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5525,uu____5526)
                          ->
                          let uu____5535 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____5535 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____5575 ->
                                    let rank =
                                      let uu____5582 = is_top_level_prob prob
                                         in
                                      if uu____5582
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____5584 =
                                      let uu___148_5587 = tp  in
                                      let uu____5590 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___148_5587.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___148_5587.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___148_5587.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5590;
                                        FStar_TypeChecker_Common.element =
                                          (uu___148_5587.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___148_5587.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___148_5587.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___148_5587.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___148_5587.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___148_5587.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____5584)))
                      | (uu____5600,FStar_Syntax_Syntax.Tm_uvar uu____5601)
                          ->
                          let uu____5610 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____5610 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____5650 ->
                                    let uu____5656 =
                                      let uu___149_5661 = tp  in
                                      let uu____5664 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___149_5661.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5664;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___149_5661.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___149_5661.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___149_5661.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___149_5661.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___149_5661.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___149_5661.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___149_5661.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___149_5661.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____5656)))
                      | (uu____5680,uu____5681) -> (rigid_rigid, tp)  in
                    (match uu____5472 with
                     | (rank,tp1) ->
                         let uu____5692 =
                           FStar_All.pipe_right
                             (let uu___150_5695 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___150_5695.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___150_5695.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___150_5695.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___150_5695.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___150_5695.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___150_5695.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___150_5695.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___150_5695.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___150_5695.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_43  ->
                                FStar_TypeChecker_Common.TProb _0_43)
                            in
                         (rank, uu____5692))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5701 =
            FStar_All.pipe_right
              (let uu___151_5704 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___151_5704.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___151_5704.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___151_5704.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___151_5704.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___151_5704.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___151_5704.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___151_5704.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___151_5704.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___151_5704.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44)
             in
          (rigid_rigid, uu____5701)
  
let next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____5736 probs =
      match uu____5736 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5766 = rank wl hd1  in
               (match uu____5766 with
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
    match projectee with | UDeferred _0 -> true | uu____5834 -> false
  
let __proj__UDeferred__item___0 : univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let uu___is_USolved : univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5846 -> false
  
let __proj__USolved__item___0 : univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let uu___is_UFailed : univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5858 -> false
  
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
                        let uu____5895 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____5895 with
                        | (k,uu____5899) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Unionfind.equivalent v1 v2
                             | uu____5904 -> false)))
            | uu____5905 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
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
                        let uu____5948 =
                          really_solve_universe_eq pid_orig wl1 u13 u23  in
                        (match uu____5948 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5951 -> USolved wl1  in
                  aux wl us1 us2
                else
                  (let uu____5957 =
                     let uu____5958 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____5959 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5958
                       uu____5959
                      in
                   UFailed uu____5957)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5975 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____5975 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5993 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____5993 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____5996 ->
                let uu____5999 =
                  let uu____6000 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____6001 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____6000
                    uu____6001 msg
                   in
                UFailed uu____5999
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____6002,uu____6003) ->
              let uu____6004 =
                let uu____6005 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____6006 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6005 uu____6006
                 in
              failwith uu____6004
          | (FStar_Syntax_Syntax.U_unknown ,uu____6007) ->
              let uu____6008 =
                let uu____6009 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____6010 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6009 uu____6010
                 in
              failwith uu____6008
          | (uu____6011,FStar_Syntax_Syntax.U_bvar uu____6012) ->
              let uu____6013 =
                let uu____6014 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____6015 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6014 uu____6015
                 in
              failwith uu____6013
          | (uu____6016,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____6017 =
                let uu____6018 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____6019 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6018 uu____6019
                 in
              failwith uu____6017
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____6031 = FStar_Unionfind.equivalent v1 v2  in
              if uu____6031
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____6042 = occurs_univ v1 u3  in
              if uu____6042
              then
                let uu____6043 =
                  let uu____6044 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____6045 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6044 uu____6045
                   in
                try_umax_components u11 u21 uu____6043
              else
                (let uu____6047 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____6047)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____6055 = occurs_univ v1 u3  in
              if uu____6055
              then
                let uu____6056 =
                  let uu____6057 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____6058 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6057 uu____6058
                   in
                try_umax_components u11 u21 uu____6056
              else
                (let uu____6060 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____6060)
          | (FStar_Syntax_Syntax.U_max uu____6063,uu____6064) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____6069 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____6069
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____6071,FStar_Syntax_Syntax.U_max uu____6072) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____6077 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____6077
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____6079,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____6080,FStar_Syntax_Syntax.U_name
             uu____6081) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____6082) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____6083) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6084,FStar_Syntax_Syntax.U_succ
             uu____6085) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6086,FStar_Syntax_Syntax.U_zero
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
  let uu____6148 = bc1  in
  match uu____6148 with
  | (bs1,mk_cod1) ->
      let uu____6173 = bc2  in
      (match uu____6173 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6220 = FStar_Util.first_N n1 bs  in
             match uu____6220 with
             | (bs3,rest) ->
                 let uu____6234 = mk_cod rest  in (bs3, uu____6234)
              in
           let l1 = FStar_List.length bs1  in
           let l2 = FStar_List.length bs2  in
           if l1 = l2
           then
             let uu____6252 =
               let uu____6256 = mk_cod1 []  in (bs1, uu____6256)  in
             let uu____6258 =
               let uu____6262 = mk_cod2 []  in (bs2, uu____6262)  in
             (uu____6252, uu____6258)
           else
             if l1 > l2
             then
               (let uu____6284 = curry l2 bs1 mk_cod1  in
                let uu____6291 =
                  let uu____6295 = mk_cod2 []  in (bs2, uu____6295)  in
                (uu____6284, uu____6291))
             else
               (let uu____6304 =
                  let uu____6308 = mk_cod1 []  in (bs1, uu____6308)  in
                let uu____6310 = curry l1 bs2 mk_cod2  in
                (uu____6304, uu____6310)))
  
let rec solve : FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6414 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____6414
       then
         let uu____6415 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6415
       else ());
      (let uu____6417 = next_prob probs  in
       match uu____6417 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___152_6430 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___152_6430.wl_deferred);
               ctr = (uu___152_6430.ctr);
               defer_ok = (uu___152_6430.defer_ok);
               smt_ok = (uu___152_6430.smt_ok);
               tcenv = (uu___152_6430.tcenv)
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
                  let uu____6437 = solve_flex_rigid_join env tp probs1  in
                  (match uu____6437 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6441 = solve_rigid_flex_meet env tp probs1  in
                     match uu____6441 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____6445,uu____6446) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6455 ->
                let uu____6460 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6488  ->
                          match uu____6488 with
                          | (c,uu____6493,uu____6494) -> c < probs.ctr))
                   in
                (match uu____6460 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6516 =
                            FStar_List.map
                              (fun uu____6522  ->
                                 match uu____6522 with
                                 | (uu____6528,x,y) -> (x, y))
                              probs.wl_deferred
                             in
                          Success uu____6516
                      | uu____6531 ->
                          let uu____6536 =
                            let uu___153_6537 = probs  in
                            let uu____6538 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6547  ->
                                      match uu____6547 with
                                      | (uu____6551,uu____6552,y) -> y))
                               in
                            {
                              attempting = uu____6538;
                              wl_deferred = rest;
                              ctr = (uu___153_6537.ctr);
                              defer_ok = (uu___153_6537.defer_ok);
                              smt_ok = (uu___153_6537.smt_ok);
                              tcenv = (uu___153_6537.tcenv)
                            }  in
                          solve env uu____6536))))

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
            let uu____6559 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____6559 with
            | USolved wl1 ->
                let uu____6561 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____6561
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
                  let uu____6595 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____6595 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6598 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6606;
                  FStar_Syntax_Syntax.pos = uu____6607;
                  FStar_Syntax_Syntax.vars = uu____6608;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6611;
                  FStar_Syntax_Syntax.pos = uu____6612;
                  FStar_Syntax_Syntax.vars = uu____6613;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6625,uu____6626) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6631,FStar_Syntax_Syntax.Tm_uinst uu____6632) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6637 -> USolved wl

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
            ((let uu____6645 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____6645
              then
                let uu____6646 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6646 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

and solve_rigid_flex_meet :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6654 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____6654
         then
           let uu____6655 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6655
         else ());
        (let uu____6657 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____6657 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6699 = head_matches_delta env () t1 t2  in
               match uu____6699 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6721 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____6747 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____6756 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____6757 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____6756, uu____6757)
                          | FStar_Pervasives_Native.None  ->
                              let uu____6760 = FStar_Syntax_Subst.compress t1
                                 in
                              let uu____6761 = FStar_Syntax_Subst.compress t2
                                 in
                              (uu____6760, uu____6761)
                           in
                        (match uu____6747 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6783 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_45  ->
                                    FStar_TypeChecker_Common.TProb _0_45)
                                 uu____6783
                                in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6806 =
                                    let uu____6812 =
                                      let uu____6815 =
                                        let uu____6818 =
                                          let uu____6819 =
                                            let uu____6824 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2
                                               in
                                            (x, uu____6824)  in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6819
                                           in
                                        FStar_Syntax_Syntax.mk uu____6818  in
                                      uu____6815 FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____6837 =
                                      let uu____6839 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort
                                         in
                                      [uu____6839]  in
                                    (uu____6812, uu____6837)  in
                                  FStar_Pervasives_Native.Some uu____6806
                              | (uu____6848,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6850)) ->
                                  let uu____6855 =
                                    let uu____6859 =
                                      let uu____6861 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11
                                         in
                                      [uu____6861]  in
                                    (t11, uu____6859)  in
                                  FStar_Pervasives_Native.Some uu____6855
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6867),uu____6868) ->
                                  let uu____6873 =
                                    let uu____6877 =
                                      let uu____6879 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21
                                         in
                                      [uu____6879]  in
                                    (t21, uu____6877)  in
                                  FStar_Pervasives_Native.Some uu____6873
                              | uu____6884 ->
                                  let uu____6887 =
                                    FStar_Syntax_Util.head_and_args t11  in
                                  (match uu____6887 with
                                   | (head1,uu____6902) ->
                                       let uu____6917 =
                                         let uu____6918 =
                                           FStar_Syntax_Util.un_uinst head1
                                            in
                                         uu____6918.FStar_Syntax_Syntax.n  in
                                       (match uu____6917 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6925;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6927;_}
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
                                        | uu____6936 ->
                                            FStar_Pervasives_Native.None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6945) ->
                  let uu____6958 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___127_6967  ->
                            match uu___127_6967 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____6972 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____6972 with
                                      | (u',uu____6983) ->
                                          let uu____6998 =
                                            let uu____6999 = whnf env u'  in
                                            uu____6999.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____6998 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____7003) ->
                                               FStar_Unionfind.equivalent uv
                                                 uv'
                                           | uu____7019 -> false))
                                 | uu____7020 -> false)
                            | uu____7022 -> false))
                     in
                  (match uu____6958 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____7043 tps =
                         match uu____7043 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____7070 =
                                    let uu____7075 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound uu____7075  in
                                  (match uu____7070 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____7094 -> FStar_Pervasives_Native.None)
                          in
                       let uu____7099 =
                         let uu____7104 =
                           let uu____7108 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (uu____7108, [])  in
                         make_lower_bound uu____7104 lower_bounds  in
                       (match uu____7099 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____7115 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____7115
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
                            ((let uu____7128 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____7128
                              then
                                let wl' =
                                  let uu___154_7130 = wl  in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___154_7130.wl_deferred);
                                    ctr = (uu___154_7130.ctr);
                                    defer_ok = (uu___154_7130.defer_ok);
                                    smt_ok = (uu___154_7130.smt_ok);
                                    tcenv = (uu___154_7130.tcenv)
                                  }  in
                                let uu____7131 = wl_to_string wl'  in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____7131
                              else ());
                             (let uu____7133 =
                                solve_t env eq_prob
                                  (let uu___155_7134 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___155_7134.wl_deferred);
                                     ctr = (uu___155_7134.ctr);
                                     defer_ok = (uu___155_7134.defer_ok);
                                     smt_ok = (uu___155_7134.smt_ok);
                                     tcenv = (uu___155_7134.tcenv)
                                   })
                                 in
                              match uu____7133 with
                              | Success uu____7136 ->
                                  let wl1 =
                                    let uu___156_7138 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___156_7138.wl_deferred);
                                      ctr = (uu___156_7138.ctr);
                                      defer_ok = (uu___156_7138.defer_ok);
                                      smt_ok = (uu___156_7138.smt_ok);
                                      tcenv = (uu___156_7138.tcenv)
                                    }  in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1
                                     in
                                  let uu____7140 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds
                                     in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____7143 -> FStar_Pervasives_Native.None))))
              | uu____7144 -> failwith "Impossible: Not a rigid-flex"))

and solve_flex_rigid_join :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____7151 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____7151
         then
           let uu____7152 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7152
         else ());
        (let uu____7154 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____7154 with
         | (u,args) ->
             let uu____7181 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____7181 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i  in
                  let base_types_match t1 t2 =
                    let uu____7212 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____7212 with
                    | (h1,args1) ->
                        let uu____7240 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____7240 with
                         | (h2,uu____7253) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7272 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  if uu____7272
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____7285 =
                                          let uu____7287 =
                                            let uu____7288 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_46  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_46) uu____7288
                                             in
                                          [uu____7287]  in
                                        FStar_Pervasives_Native.Some
                                          uu____7285))
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
                                       (let uu____7310 =
                                          let uu____7312 =
                                            let uu____7313 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_47  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_47) uu____7313
                                             in
                                          [uu____7312]  in
                                        FStar_Pervasives_Native.Some
                                          uu____7310))
                                  else FStar_Pervasives_Native.None
                              | uu____7321 -> FStar_Pervasives_Native.None))
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
                             let uu____7387 =
                               let uu____7393 =
                                 let uu____7396 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21  in
                                 FStar_Syntax_Util.refine x1 uu____7396  in
                               (uu____7393, m1)  in
                             FStar_Pervasives_Native.Some uu____7387)
                    | (uu____7405,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7407)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7439),uu____7440) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____7471 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7505) ->
                       let uu____7518 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___128_7527  ->
                                 match uu___128_7527 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____7532 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____7532 with
                                           | (u',uu____7543) ->
                                               let uu____7558 =
                                                 let uu____7559 = whnf env u'
                                                    in
                                                 uu____7559.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____7558 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7563) ->
                                                    FStar_Unionfind.equivalent
                                                      uv uv'
                                                | uu____7579 -> false))
                                      | uu____7580 -> false)
                                 | uu____7582 -> false))
                          in
                       (match uu____7518 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7607 tps =
                              match uu____7607 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7648 =
                                         let uu____7655 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound uu____7655  in
                                       (match uu____7648 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____7690 ->
                                       FStar_Pervasives_Native.None)
                               in
                            let uu____7697 =
                              let uu____7704 =
                                let uu____7710 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (uu____7710, [])  in
                              make_upper_bound uu____7704 upper_bounds  in
                            (match uu____7697 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____7719 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____7719
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
                                 ((let uu____7738 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____7738
                                   then
                                     let wl' =
                                       let uu___157_7740 = wl  in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___157_7740.wl_deferred);
                                         ctr = (uu___157_7740.ctr);
                                         defer_ok = (uu___157_7740.defer_ok);
                                         smt_ok = (uu___157_7740.smt_ok);
                                         tcenv = (uu___157_7740.tcenv)
                                       }  in
                                     let uu____7741 = wl_to_string wl'  in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7741
                                   else ());
                                  (let uu____7743 =
                                     solve_t env eq_prob
                                       (let uu___158_7744 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___158_7744.wl_deferred);
                                          ctr = (uu___158_7744.ctr);
                                          defer_ok = (uu___158_7744.defer_ok);
                                          smt_ok = (uu___158_7744.smt_ok);
                                          tcenv = (uu___158_7744.tcenv)
                                        })
                                      in
                                   match uu____7743 with
                                   | Success uu____7746 ->
                                       let wl1 =
                                         let uu___159_7748 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___159_7748.wl_deferred);
                                           ctr = (uu___159_7748.ctr);
                                           defer_ok =
                                             (uu___159_7748.defer_ok);
                                           smt_ok = (uu___159_7748.smt_ok);
                                           tcenv = (uu___159_7748.tcenv)
                                         }  in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1
                                          in
                                       let uu____7750 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds
                                          in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____7753 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____7754 -> failwith "Impossible: Not a flex-rigid")))

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
                    ((let uu____7819 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____7819
                      then
                        let uu____7820 = prob_to_string env1 rhs_prob  in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7820
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst
                         in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___160_7852 = hd1  in
                      let uu____7853 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___160_7852.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___160_7852.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7853
                      }  in
                    let hd21 =
                      let uu___161_7857 = hd2  in
                      let uu____7858 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___161_7857.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___161_7857.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7858
                      }  in
                    let prob =
                      let uu____7862 =
                        let uu____7865 =
                          FStar_All.pipe_left invert_rel (p_rel orig)  in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7865 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter"
                         in
                      FStar_All.pipe_left
                        (fun _0_48  -> FStar_TypeChecker_Common.TProb _0_48)
                        uu____7862
                       in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                    let subst2 =
                      let uu____7873 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1
                         in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7873
                       in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                    let uu____7876 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1  in
                    (match uu____7876 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7894 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst
                              in
                           let uu____7897 =
                             close_forall env2 [(hd12, imp)] phi  in
                           FStar_Syntax_Util.mk_conj uu____7894 uu____7897
                            in
                         ((let uu____7903 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____7903
                           then
                             let uu____7904 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____7905 =
                               FStar_Syntax_Print.bv_to_string hd12  in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7904 uu____7905
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7920 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch"
                 in
              let scope = p_scope orig  in
              let uu____7926 = aux scope env [] bs1 bs2  in
              match uu____7926 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl
                     in
                  solve env (attempt sub_probs wl1)

and solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7942 = compress_tprob wl problem  in
        solve_t' env uu____7942 wl

and solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7975 = head_matches_delta env1 wl1 t1 t2  in
          match uu____7975 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____7992,uu____7993) ->
                   let rec may_relate head3 =
                     let uu____8008 =
                       let uu____8009 = FStar_Syntax_Subst.compress head3  in
                       uu____8009.FStar_Syntax_Syntax.n  in
                     match uu____8008 with
                     | FStar_Syntax_Syntax.Tm_name uu____8012 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____8013 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____8031,uu____8032) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____8062) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____8068) ->
                         may_relate t
                     | uu____8073 -> false  in
                   let uu____8074 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok
                      in
                   if uu____8074
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
                                let uu____8091 =
                                  let uu____8092 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____8092 t21
                                   in
                                FStar_Syntax_Util.mk_forall u_x x uu____8091
                             in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1)
                        in
                     let uu____8094 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1
                        in
                     solve env1 uu____8094
                   else giveup env1 "head mismatch" orig
               | (uu____8096,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___162_8104 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___162_8104.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___162_8104.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___162_8104.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___162_8104.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___162_8104.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___162_8104.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___162_8104.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___162_8104.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____8105,FStar_Pervasives_Native.None ) ->
                   ((let uu____8112 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____8112
                     then
                       let uu____8113 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____8114 = FStar_Syntax_Print.tag_of_term t1  in
                       let uu____8115 = FStar_Syntax_Print.term_to_string t2
                          in
                       let uu____8116 = FStar_Syntax_Print.tag_of_term t2  in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____8113
                         uu____8114 uu____8115 uu____8116
                     else ());
                    (let uu____8118 = FStar_Syntax_Util.head_and_args t1  in
                     match uu____8118 with
                     | (head11,args1) ->
                         let uu____8144 = FStar_Syntax_Util.head_and_args t2
                            in
                         (match uu____8144 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1  in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____8184 =
                                  let uu____8185 =
                                    FStar_Syntax_Print.term_to_string head11
                                     in
                                  let uu____8186 = args_to_string args1  in
                                  let uu____8187 =
                                    FStar_Syntax_Print.term_to_string head21
                                     in
                                  let uu____8188 = args_to_string args2  in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____8185 uu____8186 uu____8187
                                    uu____8188
                                   in
                                giveup env1 uu____8184 orig
                              else
                                (let uu____8190 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____8193 =
                                        FStar_Syntax_Util.eq_args args1 args2
                                         in
                                      uu____8193 = FStar_Syntax_Util.Equal)
                                    in
                                 if uu____8190
                                 then
                                   let uu____8194 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1
                                      in
                                   match uu____8194 with
                                   | USolved wl2 ->
                                       let uu____8196 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2
                                          in
                                       solve env1 uu____8196
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____8200 =
                                      base_and_refinement env1 wl1 t1  in
                                    match uu____8200 with
                                    | (base1,refinement1) ->
                                        let uu____8226 =
                                          base_and_refinement env1 wl1 t2  in
                                        (match uu____8226 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____8280 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1
                                                     in
                                                  (match uu____8280 with
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
                                                           (fun uu____8290 
                                                              ->
                                                              fun uu____8291 
                                                                ->
                                                                match 
                                                                  (uu____8290,
                                                                    uu____8291)
                                                                with
                                                                | ((a,uu____8301),
                                                                   (a',uu____8303))
                                                                    ->
                                                                    let uu____8308
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
                                                                    _0_49  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_49)
                                                                    uu____8308)
                                                           args1 args2
                                                          in
                                                       let formula =
                                                         let uu____8314 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8314
                                                          in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2
                                                          in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8318 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1)
                                                     in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2)
                                                     in
                                                  solve_t env1
                                                    (let uu___163_8351 =
                                                       problem  in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___163_8351.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___163_8351.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___163_8351.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___163_8351.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___163_8351.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___163_8351.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___163_8351.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___163_8351.FStar_TypeChecker_Common.rank)
                                                     }) wl1))))))))
           in
        let imitate orig env1 wl1 p =
          let uu____8371 = p  in
          match uu____8371 with
          | (((u,k),xs,c),ps,(h,uu____8382,qs)) ->
              let xs1 = sn_binders env1 xs  in
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____8431 = imitation_sub_probs orig env1 xs1 ps qs  in
              (match uu____8431 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8445 = h gs_xs  in
                     let uu____8446 =
                       let uu____8453 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_50  -> FStar_Util.Inl _0_50)
                          in
                       FStar_All.pipe_right uu____8453
                         (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                        in
                     FStar_Syntax_Util.abs xs1 uu____8445 uu____8446  in
                   ((let uu____8484 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____8484
                     then
                       let uu____8485 =
                         FStar_Syntax_Print.binders_to_string ", " xs1  in
                       let uu____8486 = FStar_Syntax_Print.comp_to_string c
                          in
                       let uu____8487 = FStar_Syntax_Print.term_to_string im
                          in
                       let uu____8488 = FStar_Syntax_Print.tag_of_term im  in
                       let uu____8489 =
                         let uu____8490 =
                           FStar_List.map (prob_to_string env1) sub_probs  in
                         FStar_All.pipe_right uu____8490
                           (FStar_String.concat ", ")
                          in
                       let uu____8493 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula
                          in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8485 uu____8486 uu____8487 uu____8488
                         uu____8489 uu____8493
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1
                        in
                     solve env1 (attempt sub_probs wl2))))
           in
        let imitate' orig env1 wl1 uu___129_8511 =
          match uu___129_8511 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p  in
        let project orig env1 wl1 i p =
          let uu____8540 = p  in
          match uu____8540 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____8598 = FStar_List.nth ps i  in
              (match uu____8598 with
               | (pi,uu____8601) ->
                   let uu____8606 = FStar_List.nth xs i  in
                   (match uu____8606 with
                    | (xi,uu____8613) ->
                        let rec gs k =
                          let uu____8622 = FStar_Syntax_Util.arrow_formals k
                             in
                          match uu____8622 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8674)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort
                                       in
                                    let uu____8682 = new_uvar r xs k_a  in
                                    (match uu____8682 with
                                     | (gi_xs,gi) ->
                                         let gi_xs1 =
                                           FStar_TypeChecker_Normalize.eta_expand
                                             env1 gi_xs
                                            in
                                         let gi_ps =
                                           (FStar_Syntax_Syntax.mk_Tm_app gi
                                              ps)
                                             (FStar_Pervasives_Native.Some
                                                (k_a.FStar_Syntax_Syntax.n))
                                             r
                                            in
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT
                                              (a, gi_xs1))
                                           :: subst1  in
                                         let uu____8701 = aux subst2 tl1  in
                                         (match uu____8701 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8716 =
                                                let uu____8718 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1
                                                   in
                                                uu____8718 :: gi_xs'  in
                                              let uu____8719 =
                                                let uu____8721 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps
                                                   in
                                                uu____8721 :: gi_ps'  in
                                              (uu____8716, uu____8719)))
                                 in
                              aux [] bs
                           in
                        let uu____8724 =
                          let uu____8725 = matches pi  in
                          FStar_All.pipe_left Prims.op_Negation uu____8725
                           in
                        if uu____8724
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____8728 = gs xi.FStar_Syntax_Syntax.sort
                              in
                           match uu____8728 with
                           | (g_xs,uu____8735) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                  in
                               let proj =
                                 let uu____8742 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     FStar_Pervasives_Native.None r
                                    in
                                 let uu____8747 =
                                   let uu____8754 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_52  -> FStar_Util.Inl _0_52)
                                      in
                                   FStar_All.pipe_right uu____8754
                                     (fun _0_53  ->
                                        FStar_Pervasives_Native.Some _0_53)
                                    in
                                 FStar_Syntax_Util.abs xs uu____8742
                                   uu____8747
                                  in
                               let sub1 =
                                 let uu____8785 =
                                   let uu____8788 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       FStar_Pervasives_Native.None r
                                      in
                                   let uu____8795 =
                                     let uu____8798 =
                                       FStar_List.map
                                         (fun uu____8804  ->
                                            match uu____8804 with
                                            | (uu____8809,uu____8810,y) -> y)
                                         qs
                                        in
                                     FStar_All.pipe_left h uu____8798  in
                                   mk_problem (p_scope orig) orig uu____8788
                                     (p_rel orig) uu____8795
                                     FStar_Pervasives_Native.None
                                     "projection"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_54  ->
                                      FStar_TypeChecker_Common.TProb _0_54)
                                   uu____8785
                                  in
                               ((let uu____8820 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____8820
                                 then
                                   let uu____8821 =
                                     FStar_Syntax_Print.term_to_string proj
                                      in
                                   let uu____8822 = prob_to_string env1 sub1
                                      in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8821 uu____8822
                                 else ());
                                (let wl2 =
                                   let uu____8825 =
                                     let uu____8827 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1)
                                        in
                                     FStar_Pervasives_Native.Some uu____8827
                                      in
                                   solve_prob orig uu____8825
                                     [TERM (u, proj)] wl1
                                    in
                                 let uu____8832 =
                                   solve env1 (attempt [sub1] wl2)  in
                                 FStar_All.pipe_left
                                   (fun _0_55  ->
                                      FStar_Pervasives_Native.Some _0_55)
                                   uu____8832)))))
           in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8856 = lhs  in
          match uu____8856 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8879 = FStar_Syntax_Util.arrow_formals_comp k_uv
                   in
                match uu____8879 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8901 =
                        let uu____8927 = decompose env t2  in
                        (((uv, k_uv), xs, c), ps, uu____8927)  in
                      FStar_Pervasives_Native.Some uu____8901
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv
                          in
                       let rec elim k args =
                         let uu____9010 =
                           let uu____9014 =
                             let uu____9015 = FStar_Syntax_Subst.compress k
                                in
                             uu____9015.FStar_Syntax_Syntax.n  in
                           (uu____9014, args)  in
                         match uu____9010 with
                         | (uu____9022,[]) ->
                             let uu____9024 =
                               let uu____9030 =
                                 FStar_Syntax_Syntax.mk_Total k  in
                               ([], uu____9030)  in
                             FStar_Pervasives_Native.Some uu____9024
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____9041,uu____9042) ->
                             let uu____9053 =
                               FStar_Syntax_Util.head_and_args k  in
                             (match uu____9053 with
                              | (uv1,uv_args) ->
                                  let uu____9082 =
                                    let uu____9083 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____9083.FStar_Syntax_Syntax.n  in
                                  (match uu____9082 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9090) ->
                                       let uu____9103 =
                                         pat_vars env [] uv_args  in
                                       (match uu____9103 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9117  ->
                                                      let uu____9118 =
                                                        let uu____9119 =
                                                          let uu____9120 =
                                                            let uu____9123 =
                                                              let uu____9124
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____9124
                                                                FStar_Pervasives_Native.fst
                                                               in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9123
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____9120
                                                           in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9119
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9118))
                                               in
                                            let c1 =
                                              let uu____9130 =
                                                let uu____9131 =
                                                  let uu____9134 =
                                                    let uu____9135 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____9135
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9134
                                                   in
                                                FStar_Pervasives_Native.fst
                                                  uu____9131
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9130
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____9144 =
                                                let uu____9151 =
                                                  let uu____9157 =
                                                    let uu____9158 =
                                                      let uu____9161 =
                                                        let uu____9162 =
                                                          FStar_Syntax_Util.type_u
                                                            ()
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____9162
                                                          FStar_Pervasives_Native.fst
                                                         in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9161
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9158
                                                     in
                                                  FStar_Util.Inl uu____9157
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____9151
                                                 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9144
                                               in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____9185 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app uu____9188,uu____9189)
                             ->
                             let uu____9201 =
                               FStar_Syntax_Util.head_and_args k  in
                             (match uu____9201 with
                              | (uv1,uv_args) ->
                                  let uu____9230 =
                                    let uu____9231 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____9231.FStar_Syntax_Syntax.n  in
                                  (match uu____9230 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9238) ->
                                       let uu____9251 =
                                         pat_vars env [] uv_args  in
                                       (match uu____9251 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9265  ->
                                                      let uu____9266 =
                                                        let uu____9267 =
                                                          let uu____9268 =
                                                            let uu____9271 =
                                                              let uu____9272
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____9272
                                                                FStar_Pervasives_Native.fst
                                                               in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9271
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____9268
                                                           in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9267
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9266))
                                               in
                                            let c1 =
                                              let uu____9278 =
                                                let uu____9279 =
                                                  let uu____9282 =
                                                    let uu____9283 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____9283
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9282
                                                   in
                                                FStar_Pervasives_Native.fst
                                                  uu____9279
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9278
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____9292 =
                                                let uu____9299 =
                                                  let uu____9305 =
                                                    let uu____9306 =
                                                      let uu____9309 =
                                                        let uu____9310 =
                                                          FStar_Syntax_Util.type_u
                                                            ()
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____9310
                                                          FStar_Pervasives_Native.fst
                                                         in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9309
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9306
                                                     in
                                                  FStar_Util.Inl uu____9305
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____9299
                                                 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9292
                                               in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____9333 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____9338)
                             ->
                             let n_args = FStar_List.length args  in
                             let n_xs = FStar_List.length xs1  in
                             if n_xs = n_args
                             then
                               let uu____9364 =
                                 FStar_Syntax_Subst.open_comp xs1 c1  in
                               FStar_All.pipe_right uu____9364
                                 (fun _0_56  ->
                                    FStar_Pervasives_Native.Some _0_56)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9383 =
                                    FStar_Util.first_N n_xs args  in
                                  match uu____9383 with
                                  | (args1,rest) ->
                                      let uu____9399 =
                                        FStar_Syntax_Subst.open_comp xs1 c1
                                         in
                                      (match uu____9399 with
                                       | (xs2,c2) ->
                                           let uu____9407 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest
                                              in
                                           FStar_Util.bind_opt uu____9407
                                             (fun uu____9418  ->
                                                match uu____9418 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9440 =
                                    FStar_Util.first_N n_args xs1  in
                                  match uu____9440 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1)))
                                          FStar_Pervasives_Native.None
                                          k.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____9486 =
                                        let uu____9489 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9489
                                         in
                                      FStar_All.pipe_right uu____9486
                                        (fun _0_57  ->
                                           FStar_Pervasives_Native.Some _0_57))
                         | uu____9497 ->
                             let uu____9501 =
                               let uu____9502 =
                                 FStar_Syntax_Print.uvar_to_string uv  in
                               let uu____9506 =
                                 FStar_Syntax_Print.term_to_string k  in
                               let uu____9507 =
                                 FStar_Syntax_Print.term_to_string k_uv1  in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9502 uu____9506 uu____9507
                                in
                             failwith uu____9501
                          in
                       let uu____9511 = elim k_uv1 ps  in
                       FStar_Util.bind_opt uu____9511
                         (fun uu____9539  ->
                            match uu____9539 with
                            | (xs1,c1) ->
                                let uu____9567 =
                                  let uu____9590 = decompose env t2  in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9590)
                                   in
                                FStar_Pervasives_Native.Some uu____9567))
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
                     let uu____9662 = imitate orig env wl1 st  in
                     match uu____9662 with
                     | Failed uu____9667 ->
                         (FStar_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9673 = project orig env wl1 i st  in
                      match uu____9673 with
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some (Failed uu____9680) ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some sol -> sol))
                 in
              let check_head fvs1 t21 =
                let uu____9694 = FStar_Syntax_Util.head_and_args t21  in
                match uu____9694 with
                | (hd1,uu____9705) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9720 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9728 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____9729 -> true
                     | uu____9744 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1  in
                         let uu____9747 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1  in
                         if uu____9747
                         then true
                         else
                           ((let uu____9750 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____9750
                             then
                               let uu____9751 = names_to_string fvs_hd  in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____9751
                             else ());
                            false))
                 in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____9759 =
                    let uu____9762 = FStar_Syntax_Util.head_and_args t21  in
                    FStar_All.pipe_right uu____9762
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____9759 FStar_Syntax_Free.names  in
                let uu____9793 = FStar_Util.set_is_empty fvs_hd  in
                if uu____9793
                then ~- (Prims.parse_int "1")
                else (Prims.parse_int "0")  in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1  in
                   let t21 = sn env t2  in
                   let fvs1 = FStar_Syntax_Free.names t11  in
                   let fvs2 = FStar_Syntax_Free.names t21  in
                   let uu____9802 = occurs_check env wl1 (uv, k_uv) t21  in
                   (match uu____9802 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____9810 =
                            let uu____9811 = FStar_Option.get msg  in
                            Prims.strcat "occurs-check failed: " uu____9811
                             in
                          giveup_or_defer1 orig uu____9810
                        else
                          (let uu____9813 =
                             FStar_Util.set_is_subset_of fvs2 fvs1  in
                           if uu____9813
                           then
                             let uu____9814 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
                                in
                             (if uu____9814
                              then
                                let uu____9815 = subterms args_lhs  in
                                imitate' orig env wl1 uu____9815
                              else
                                ((let uu____9819 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____9819
                                  then
                                    let uu____9820 =
                                      FStar_Syntax_Print.term_to_string t11
                                       in
                                    let uu____9821 = names_to_string fvs1  in
                                    let uu____9822 = names_to_string fvs2  in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9820 uu____9821 uu____9822
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9827 ->
                                        let uu____9828 = sn_binders env vars
                                           in
                                        u_abs k_uv uu____9828 t21
                                     in
                                  let wl2 =
                                    solve_prob orig
                                      FStar_Pervasives_Native.None
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
                               (let uu____9837 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21)
                                   in
                                if uu____9837
                                then
                                  ((let uu____9839 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____9839
                                    then
                                      let uu____9840 =
                                        FStar_Syntax_Print.term_to_string t11
                                         in
                                      let uu____9841 = names_to_string fvs1
                                         in
                                      let uu____9842 = names_to_string fvs2
                                         in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9840 uu____9841 uu____9842
                                    else ());
                                   (let uu____9844 = subterms args_lhs  in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9844
                                      (~- (Prims.parse_int "1"))))
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
                     (let uu____9855 =
                        let uu____9856 = FStar_Syntax_Free.names t1  in
                        check_head uu____9856 t2  in
                      if uu____9855
                      then
                        let im_ok = imitate_ok t2  in
                        ((let uu____9860 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel")
                             in
                          if uu____9860
                          then
                            let uu____9861 =
                              FStar_Syntax_Print.term_to_string t1  in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9861
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9864 = subterms args_lhs  in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9864 im_ok))
                      else giveup env "head-symbol is free" orig))
           in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9906 =
               match uu____9906 with
               | (t,u,k,args) ->
                   let k1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta] env k
                      in
                   let uu____9937 = FStar_Syntax_Util.arrow_formals k1  in
                   (match uu____9937 with
                    | (all_formals,uu____9948) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____10040  ->
                                        match uu____10040 with
                                        | (x,imp) ->
                                            let uu____10047 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            (uu____10047, imp)))
                                 in
                              let pattern_vars1 = FStar_List.rev pattern_vars
                                 in
                              let kk =
                                let uu____10055 = FStar_Syntax_Util.type_u ()
                                   in
                                match uu____10055 with
                                | (t1,uu____10059) ->
                                    let uu____10060 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1
                                       in
                                    FStar_Pervasives_Native.fst uu____10060
                                 in
                              let uu____10063 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk
                                 in
                              (match uu____10063 with
                               | (t',tm_u1) ->
                                   let uu____10070 = destruct_flex_t t'  in
                                   (match uu____10070 with
                                    | (uu____10090,u1,k11,uu____10093) ->
                                        let sol =
                                          let uu____10121 =
                                            let uu____10126 =
                                              u_abs k1 all_formals t'  in
                                            ((u, k1), uu____10126)  in
                                          TERM uu____10121  in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1)
                                            FStar_Pervasives_Native.None
                                            t.FStar_Syntax_Syntax.pos
                                           in
                                        (sol, (t_app, u1, k11, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____10186 = pat_var_opt env pat_args hd1
                                 in
                              (match uu____10186 with
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
                                              (fun uu____10215  ->
                                                 match uu____10215 with
                                                 | (x,uu____10219) ->
                                                     FStar_Syntax_Syntax.bv_eq
                                                       x
                                                       (FStar_Pervasives_Native.fst
                                                          y)))
                                      in
                                   if Prims.op_Negation maybe_pat
                                   then
                                     aux pat_args pattern_vars
                                       pattern_var_set formals1 tl1
                                   else
                                     (let fvs =
                                        FStar_Syntax_Free.names
                                          (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort
                                         in
                                      let uu____10225 =
                                        let uu____10226 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set
                                           in
                                        Prims.op_Negation uu____10226  in
                                      if uu____10225
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____10230 =
                                           FStar_Util.set_add
                                             (FStar_Pervasives_Native.fst
                                                formal) pattern_var_set
                                            in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____10230 formals1
                                           tl1)))
                          | uu____10236 -> failwith "Impossible"  in
                        let uu____10247 = FStar_Syntax_Syntax.new_bv_set ()
                           in
                        aux [] [] uu____10247 all_formals args)
                in
             let solve_both_pats wl1 uu____10295 uu____10296 r =
               match (uu____10295, uu____10296) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10450 =
                     (FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)
                      in
                   if uu____10450
                   then
                     let uu____10454 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1
                        in
                     solve env uu____10454
                   else
                     (let xs1 = sn_binders env xs  in
                      let ys1 = sn_binders env ys  in
                      let zs = intersect_vars xs1 ys1  in
                      (let uu____10469 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____10469
                       then
                         let uu____10470 =
                           FStar_Syntax_Print.binders_to_string ", " xs1  in
                         let uu____10471 =
                           FStar_Syntax_Print.binders_to_string ", " ys1  in
                         let uu____10472 =
                           FStar_Syntax_Print.binders_to_string ", " zs  in
                         let uu____10473 =
                           FStar_Syntax_Print.term_to_string k1  in
                         let uu____10474 =
                           FStar_Syntax_Print.term_to_string k2  in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10470 uu____10471 uu____10472 uu____10473
                           uu____10474
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2  in
                         let args_len = FStar_List.length args  in
                         if xs_len = args_len
                         then
                           let uu____10516 =
                             FStar_Syntax_Util.subst_of_list xs2 args  in
                           FStar_Syntax_Subst.subst uu____10516 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10524 =
                                FStar_Util.first_N args_len xs2  in
                              match uu____10524 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10554 =
                                      FStar_Syntax_Syntax.mk_GTotal k  in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10554
                                     in
                                  let uu____10557 =
                                    FStar_Syntax_Util.subst_of_list xs3 args
                                     in
                                  FStar_Syntax_Subst.subst uu____10557 k3)
                           else
                             (let uu____10560 =
                                let uu____10561 =
                                  FStar_Syntax_Print.term_to_string k  in
                                let uu____10562 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2
                                   in
                                let uu____10563 =
                                  FStar_Syntax_Print.args_to_string args  in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10561 uu____10562 uu____10563
                                 in
                              failwith uu____10560)
                          in
                       let uu____10564 =
                         let uu____10570 =
                           let uu____10578 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1
                              in
                           FStar_Syntax_Util.arrow_formals uu____10578  in
                         match uu____10570 with
                         | (bs,k1') ->
                             let uu____10596 =
                               let uu____10604 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2
                                  in
                               FStar_Syntax_Util.arrow_formals uu____10604
                                in
                             (match uu____10596 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1  in
                                  let k2'_ys = subst_k k2' cs args2  in
                                  let sub_prob =
                                    let uu____10625 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_58  ->
                                         FStar_TypeChecker_Common.TProb _0_58)
                                      uu____10625
                                     in
                                  let uu____10630 =
                                    let uu____10633 =
                                      let uu____10634 =
                                        FStar_Syntax_Subst.compress k1'  in
                                      uu____10634.FStar_Syntax_Syntax.n  in
                                    let uu____10637 =
                                      let uu____10638 =
                                        FStar_Syntax_Subst.compress k2'  in
                                      uu____10638.FStar_Syntax_Syntax.n  in
                                    (uu____10633, uu____10637)  in
                                  (match uu____10630 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10646,uu____10647) ->
                                       (k1', [sub_prob])
                                   | (uu____10651,FStar_Syntax_Syntax.Tm_type
                                      uu____10652) -> (k2', [sub_prob])
                                   | uu____10656 ->
                                       let uu____10659 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____10659 with
                                        | (t,uu____10668) ->
                                            let uu____10669 = new_uvar r zs t
                                               in
                                            (match uu____10669 with
                                             | (k_zs,uu____10678) ->
                                                 let kprob =
                                                   let uu____10680 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs
                                                       FStar_Pervasives_Native.None
                                                       "flex-flex kinding"
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_59  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_59) uu____10680
                                                    in
                                                 (k_zs, [sub_prob; kprob])))))
                          in
                       match uu____10564 with
                       | (k_u',sub_probs) ->
                           let uu____10694 =
                             let uu____10702 =
                               let uu____10703 = new_uvar r zs k_u'  in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____10703
                                in
                             let uu____10708 =
                               let uu____10711 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow xs1 uu____10711  in
                             let uu____10714 =
                               let uu____10717 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow ys1 uu____10717  in
                             (uu____10702, uu____10708, uu____10714)  in
                           (match uu____10694 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs  in
                                let uu____10736 =
                                  occurs_check env wl1 (u1, k1) sub1  in
                                (match uu____10736 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1)  in
                                        let uu____10760 =
                                          FStar_Unionfind.equivalent u1 u2
                                           in
                                        if uu____10760
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
                                           let uu____10767 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2
                                              in
                                           match uu____10767 with
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
             let solve_one_pat uu____10819 uu____10820 =
               match (uu____10819, uu____10820) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10924 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____10924
                     then
                       let uu____10925 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____10926 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10925 uu____10926
                     else ());
                    (let uu____10928 = FStar_Unionfind.equivalent u1 u2  in
                     if uu____10928
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10938  ->
                              fun uu____10939  ->
                                match (uu____10938, uu____10939) with
                                | ((a,uu____10949),(t21,uu____10951)) ->
                                    let uu____10956 =
                                      let uu____10959 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      mk_problem (p_scope orig) orig
                                        uu____10959
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index"
                                       in
                                    FStar_All.pipe_right uu____10956
                                      (fun _0_60  ->
                                         FStar_TypeChecker_Common.TProb _0_60))
                           xs args2
                          in
                       let guard =
                         let uu____10963 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____10963  in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl
                          in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2  in
                        let rhs_vars = FStar_Syntax_Free.names t21  in
                        let uu____10973 = occurs_check env wl (u1, k1) t21
                           in
                        match uu____10973 with
                        | (occurs_ok,uu____10982) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs  in
                            let uu____10987 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars)
                               in
                            if uu____10987
                            then
                              let sol =
                                let uu____10989 =
                                  let uu____10994 = u_abs k1 xs t21  in
                                  ((u1, k1), uu____10994)  in
                                TERM uu____10989  in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl
                                 in
                              solve env wl1
                            else
                              (let uu____11007 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok)
                                  in
                               if uu____11007
                               then
                                 let uu____11008 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2)
                                    in
                                 match uu____11008 with
                                 | (sol,(uu____11022,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl
                                        in
                                     ((let uu____11032 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern")
                                          in
                                       if uu____11032
                                       then
                                         let uu____11033 =
                                           uvi_to_string env sol  in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____11033
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____11038 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint"))))
                in
             let uu____11040 = lhs  in
             match uu____11040 with
             | (t1,u1,k1,args1) ->
                 let uu____11045 = rhs  in
                 (match uu____11045 with
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
                       | uu____11071 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____11077 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1)
                                 in
                              match uu____11077 with
                              | (sol,uu____11084) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl  in
                                  ((let uu____11087 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern")
                                       in
                                    if uu____11087
                                    then
                                      let uu____11088 = uvi_to_string env sol
                                         in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____11088
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____11093 ->
                                        giveup env "impossible" orig))))))
           in
        let orig = FStar_TypeChecker_Common.TProb problem  in
        let uu____11095 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs
           in
        if uu____11095
        then
          let uu____11096 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____11096
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs  in
           let t2 = problem.FStar_TypeChecker_Common.rhs  in
           let uu____11100 = FStar_Util.physical_equality t1 t2  in
           if uu____11100
           then
             let uu____11101 =
               solve_prob orig FStar_Pervasives_Native.None [] wl  in
             solve env uu____11101
           else
             ((let uu____11104 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck")
                  in
               if uu____11104
               then
                 let uu____11105 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid
                    in
                 FStar_Util.print1 "Attempting %s\n" uu____11105
               else ());
              (let r = FStar_TypeChecker_Env.get_range env  in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_ascribed uu____11108,uu____11109) ->
                   let uu____11127 =
                     let uu___164_11128 = problem  in
                     let uu____11129 = FStar_Syntax_Util.unmeta t1  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___164_11128.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____11129;
                       FStar_TypeChecker_Common.relation =
                         (uu___164_11128.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___164_11128.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___164_11128.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___164_11128.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___164_11128.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___164_11128.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___164_11128.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___164_11128.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____11127 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____11130,uu____11131) ->
                   let uu____11136 =
                     let uu___164_11137 = problem  in
                     let uu____11138 = FStar_Syntax_Util.unmeta t1  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___164_11137.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____11138;
                       FStar_TypeChecker_Common.relation =
                         (uu___164_11137.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___164_11137.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___164_11137.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___164_11137.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___164_11137.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___164_11137.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___164_11137.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___164_11137.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____11136 wl
               | (uu____11139,FStar_Syntax_Syntax.Tm_ascribed uu____11140) ->
                   let uu____11158 =
                     let uu___165_11159 = problem  in
                     let uu____11160 = FStar_Syntax_Util.unmeta t2  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___165_11159.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___165_11159.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___165_11159.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____11160;
                       FStar_TypeChecker_Common.element =
                         (uu___165_11159.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___165_11159.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___165_11159.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___165_11159.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___165_11159.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___165_11159.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____11158 wl
               | (uu____11161,FStar_Syntax_Syntax.Tm_meta uu____11162) ->
                   let uu____11167 =
                     let uu___165_11168 = problem  in
                     let uu____11169 = FStar_Syntax_Util.unmeta t2  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___165_11168.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___165_11168.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___165_11168.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____11169;
                       FStar_TypeChecker_Common.element =
                         (uu___165_11168.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___165_11168.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___165_11168.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___165_11168.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___165_11168.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___165_11168.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____11167 wl
               | (FStar_Syntax_Syntax.Tm_bvar uu____11170,uu____11171) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____11172,FStar_Syntax_Syntax.Tm_bvar uu____11173) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___130_11213 =
                     match uu___130_11213 with
                     | [] -> c
                     | bs ->
                         let uu____11227 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos
                            in
                         FStar_Syntax_Syntax.mk_Total uu____11227
                      in
                   let uu____11237 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                   (match uu____11237 with
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
                                   let uu____11323 =
                                     FStar_Options.use_eq_at_higher_order ()
                                      in
                                   if uu____11323
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation
                                    in
                                 let uu____11325 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.CProb _0_61)
                                   uu____11325))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___131_11402 =
                     match uu___131_11402 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos
                      in
                   let uu____11437 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2))
                      in
                   (match uu____11437 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____11520 =
                                   let uu____11523 =
                                     FStar_Syntax_Subst.subst subst1 tbody11
                                      in
                                   let uu____11524 =
                                     FStar_Syntax_Subst.subst subst1 tbody21
                                      in
                                   mk_problem scope orig uu____11523
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____11524 FStar_Pervasives_Native.None
                                     "lambda co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_TypeChecker_Common.TProb _0_62)
                                   uu____11520))
               | (FStar_Syntax_Syntax.Tm_abs uu____11527,uu____11528) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11551 -> true
                     | uu____11566 -> false  in
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
                   let uu____11594 =
                     let uu____11605 = maybe_eta t1  in
                     let uu____11610 = maybe_eta t2  in
                     (uu____11605, uu____11610)  in
                   (match uu____11594 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_11641 = problem  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_11641.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_11641.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_11641.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_11641.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_11641.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_11641.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_11641.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_11641.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11660 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____11660
                        then
                          let uu____11661 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____11661 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11682 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____11682
                        then
                          let uu____11683 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____11683 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11688 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11699,FStar_Syntax_Syntax.Tm_abs uu____11700) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11723 -> true
                     | uu____11738 -> false  in
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
                   let uu____11766 =
                     let uu____11777 = maybe_eta t1  in
                     let uu____11782 = maybe_eta t2  in
                     (uu____11777, uu____11782)  in
                   (match uu____11766 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_11813 = problem  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_11813.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_11813.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_11813.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_11813.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_11813.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_11813.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_11813.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_11813.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11832 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____11832
                        then
                          let uu____11833 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____11833 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11854 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____11854
                        then
                          let uu____11855 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____11855 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11860 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11871,FStar_Syntax_Syntax.Tm_refine uu____11872) ->
                   let uu____11881 = as_refinement env wl t1  in
                   (match uu____11881 with
                    | (x1,phi1) ->
                        let uu____11886 = as_refinement env wl t2  in
                        (match uu____11886 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11892 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_63  ->
                                    FStar_TypeChecker_Common.TProb _0_63)
                                 uu____11892
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
                               let uu____11925 = imp phi12 phi22  in
                               FStar_All.pipe_right uu____11925
                                 (guard_on_element wl problem x11)
                                in
                             let fallback uu____11929 =
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
                                 let uu____11935 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____11935 impl
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
                                 let uu____11942 =
                                   let uu____11945 =
                                     let uu____11946 =
                                       FStar_Syntax_Syntax.mk_binder x11  in
                                     uu____11946 :: (p_scope orig)  in
                                   mk_problem uu____11945 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_TypeChecker_Common.TProb _0_64)
                                   uu____11942
                                  in
                               let uu____11949 =
                                 solve env1
                                   (let uu___167_11950 = wl  in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___167_11950.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___167_11950.smt_ok);
                                      tcenv = (uu___167_11950.tcenv)
                                    })
                                  in
                               (match uu____11949 with
                                | Failed uu____11954 -> fallback ()
                                | Success uu____11957 ->
                                    let guard =
                                      let uu____11961 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      let uu____11964 =
                                        let uu____11965 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____11965
                                          (guard_on_element wl problem x11)
                                         in
                                      FStar_Syntax_Util.mk_conj uu____11961
                                        uu____11964
                                       in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl
                                       in
                                    let wl2 =
                                      let uu___168_11972 = wl1  in
                                      {
                                        attempting =
                                          (uu___168_11972.attempting);
                                        wl_deferred =
                                          (uu___168_11972.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___168_11972.defer_ok);
                                        smt_ok = (uu___168_11972.smt_ok);
                                        tcenv = (uu___168_11972.tcenv)
                                      }  in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11974,FStar_Syntax_Syntax.Tm_uvar uu____11975) ->
                   let uu____11992 = destruct_flex_t t1  in
                   let uu____11993 = destruct_flex_t t2  in
                   flex_flex1 orig uu____11992 uu____11993
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11994;
                     FStar_Syntax_Syntax.tk = uu____11995;
                     FStar_Syntax_Syntax.pos = uu____11996;
                     FStar_Syntax_Syntax.vars = uu____11997;_},uu____11998),FStar_Syntax_Syntax.Tm_uvar
                  uu____11999) ->
                   let uu____12030 = destruct_flex_t t1  in
                   let uu____12031 = destruct_flex_t t2  in
                   flex_flex1 orig uu____12030 uu____12031
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12032,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12033;
                     FStar_Syntax_Syntax.tk = uu____12034;
                     FStar_Syntax_Syntax.pos = uu____12035;
                     FStar_Syntax_Syntax.vars = uu____12036;_},uu____12037))
                   ->
                   let uu____12068 = destruct_flex_t t1  in
                   let uu____12069 = destruct_flex_t t2  in
                   flex_flex1 orig uu____12068 uu____12069
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12070;
                     FStar_Syntax_Syntax.tk = uu____12071;
                     FStar_Syntax_Syntax.pos = uu____12072;
                     FStar_Syntax_Syntax.vars = uu____12073;_},uu____12074),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12075;
                     FStar_Syntax_Syntax.tk = uu____12076;
                     FStar_Syntax_Syntax.pos = uu____12077;
                     FStar_Syntax_Syntax.vars = uu____12078;_},uu____12079))
                   ->
                   let uu____12124 = destruct_flex_t t1  in
                   let uu____12125 = destruct_flex_t t2  in
                   flex_flex1 orig uu____12124 uu____12125
               | (FStar_Syntax_Syntax.Tm_uvar uu____12126,uu____12127) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____12136 = destruct_flex_pattern env t1  in
                   solve_t_flex_rigid false orig uu____12136 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12140;
                     FStar_Syntax_Syntax.tk = uu____12141;
                     FStar_Syntax_Syntax.pos = uu____12142;
                     FStar_Syntax_Syntax.vars = uu____12143;_},uu____12144),uu____12145)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____12168 = destruct_flex_pattern env t1  in
                   solve_t_flex_rigid false orig uu____12168 t2 wl
               | (uu____12172,FStar_Syntax_Syntax.Tm_uvar uu____12173) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____12182,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12183;
                     FStar_Syntax_Syntax.tk = uu____12184;
                     FStar_Syntax_Syntax.pos = uu____12185;
                     FStar_Syntax_Syntax.vars = uu____12186;_},uu____12187))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12210,FStar_Syntax_Syntax.Tm_type uu____12211) ->
                   solve_t' env
                     (let uu___169_12220 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12220.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12220.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12220.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12220.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12220.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12220.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12220.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12220.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12220.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12221;
                     FStar_Syntax_Syntax.tk = uu____12222;
                     FStar_Syntax_Syntax.pos = uu____12223;
                     FStar_Syntax_Syntax.vars = uu____12224;_},uu____12225),FStar_Syntax_Syntax.Tm_type
                  uu____12226) ->
                   solve_t' env
                     (let uu___169_12249 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12249.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12249.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12249.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12249.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12249.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12249.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12249.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12249.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12249.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12250,FStar_Syntax_Syntax.Tm_arrow uu____12251) ->
                   solve_t' env
                     (let uu___169_12267 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12267.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12267.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12267.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12267.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12267.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12267.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12267.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12267.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12267.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12268;
                     FStar_Syntax_Syntax.tk = uu____12269;
                     FStar_Syntax_Syntax.pos = uu____12270;
                     FStar_Syntax_Syntax.vars = uu____12271;_},uu____12272),FStar_Syntax_Syntax.Tm_arrow
                  uu____12273) ->
                   solve_t' env
                     (let uu___169_12303 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12303.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12303.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12303.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12303.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12303.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12303.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12303.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12303.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12303.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____12304,uu____12305) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation
                         in
                      let uu____12316 =
                        let uu____12317 = is_top_level_prob orig  in
                        FStar_All.pipe_left Prims.op_Negation uu____12317  in
                      if uu____12316
                      then
                        let uu____12318 =
                          FStar_All.pipe_left
                            (fun _0_65  ->
                               FStar_TypeChecker_Common.TProb _0_65)
                            (let uu___170_12321 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_12321.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_12321.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_12321.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_12321.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_12321.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_12321.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_12321.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_12321.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_12321.FStar_TypeChecker_Common.rank)
                             })
                           in
                        let uu____12322 = destruct_flex_pattern env t1  in
                        solve_t_flex_rigid false uu____12318 uu____12322 t2
                          wl
                      else
                        (let uu____12327 = base_and_refinement env wl t2  in
                         match uu____12327 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____12357 =
                                    FStar_All.pipe_left
                                      (fun _0_66  ->
                                         FStar_TypeChecker_Common.TProb _0_66)
                                      (let uu___171_12360 = problem  in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_12360.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_12360.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_12360.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_12360.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_12360.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_12360.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_12360.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_12360.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_12360.FStar_TypeChecker_Common.rank)
                                       })
                                     in
                                  let uu____12361 =
                                    destruct_flex_pattern env t1  in
                                  solve_t_flex_rigid false uu____12357
                                    uu____12361 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___172_12376 = y  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_12376.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_12376.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }  in
                                  let impl =
                                    guard_on_element wl problem y' phi  in
                                  let base_prob =
                                    let uu____12379 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_67  ->
                                         FStar_TypeChecker_Common.TProb _0_67)
                                      uu____12379
                                     in
                                  let guard =
                                    let uu____12387 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Util.mk_conj uu____12387
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
                       uu____12393;
                     FStar_Syntax_Syntax.tk = uu____12394;
                     FStar_Syntax_Syntax.pos = uu____12395;
                     FStar_Syntax_Syntax.vars = uu____12396;_},uu____12397),uu____12398)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation
                         in
                      let uu____12423 =
                        let uu____12424 = is_top_level_prob orig  in
                        FStar_All.pipe_left Prims.op_Negation uu____12424  in
                      if uu____12423
                      then
                        let uu____12425 =
                          FStar_All.pipe_left
                            (fun _0_68  ->
                               FStar_TypeChecker_Common.TProb _0_68)
                            (let uu___170_12428 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_12428.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_12428.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_12428.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_12428.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_12428.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_12428.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_12428.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_12428.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_12428.FStar_TypeChecker_Common.rank)
                             })
                           in
                        let uu____12429 = destruct_flex_pattern env t1  in
                        solve_t_flex_rigid false uu____12425 uu____12429 t2
                          wl
                      else
                        (let uu____12434 = base_and_refinement env wl t2  in
                         match uu____12434 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____12464 =
                                    FStar_All.pipe_left
                                      (fun _0_69  ->
                                         FStar_TypeChecker_Common.TProb _0_69)
                                      (let uu___171_12467 = problem  in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_12467.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_12467.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_12467.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_12467.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_12467.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_12467.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_12467.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_12467.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_12467.FStar_TypeChecker_Common.rank)
                                       })
                                     in
                                  let uu____12468 =
                                    destruct_flex_pattern env t1  in
                                  solve_t_flex_rigid false uu____12464
                                    uu____12468 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___172_12483 = y  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_12483.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_12483.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }  in
                                  let impl =
                                    guard_on_element wl problem y' phi  in
                                  let base_prob =
                                    let uu____12486 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_70  ->
                                         FStar_TypeChecker_Common.TProb _0_70)
                                      uu____12486
                                     in
                                  let guard =
                                    let uu____12494 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Util.mk_conj uu____12494
                                      impl
                                     in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl
                                     in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____12500,FStar_Syntax_Syntax.Tm_uvar uu____12501) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12511 = base_and_refinement env wl t1  in
                      match uu____12511 with
                      | (t_base,uu____12522) ->
                          solve_t env
                            (let uu___173_12537 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_12537.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_12537.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_12537.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_12537.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_12537.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_12537.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_12537.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_12537.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____12540,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12541;
                     FStar_Syntax_Syntax.tk = uu____12542;
                     FStar_Syntax_Syntax.pos = uu____12543;
                     FStar_Syntax_Syntax.vars = uu____12544;_},uu____12545))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12569 = base_and_refinement env wl t1  in
                      match uu____12569 with
                      | (t_base,uu____12580) ->
                          solve_t env
                            (let uu___173_12595 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_12595.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_12595.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_12595.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_12595.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_12595.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_12595.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_12595.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_12595.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____12598,uu____12599) ->
                   let t21 =
                     let uu____12607 = base_and_refinement env wl t2  in
                     FStar_All.pipe_left force_refinement uu____12607  in
                   solve_t env
                     (let uu___174_12620 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_12620.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___174_12620.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___174_12620.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___174_12620.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_12620.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_12620.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_12620.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_12620.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_12620.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12621,FStar_Syntax_Syntax.Tm_refine uu____12622) ->
                   let t11 =
                     let uu____12630 = base_and_refinement env wl t1  in
                     FStar_All.pipe_left force_refinement uu____12630  in
                   solve_t env
                     (let uu___175_12643 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_12643.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___175_12643.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___175_12643.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___175_12643.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_12643.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_12643.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_12643.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_12643.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_12643.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12646,uu____12647) ->
                   let head1 =
                     let uu____12666 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12666
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____12697 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12697
                       FStar_Pervasives_Native.fst
                      in
                   let uu____12725 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12725
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12734 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12734
                      then
                        let guard =
                          let uu____12741 =
                            let uu____12742 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12742 = FStar_Syntax_Util.Equal  in
                          if uu____12741
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12745 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_71  ->
                                  FStar_Pervasives_Native.Some _0_71)
                               uu____12745)
                           in
                        let uu____12747 = solve_prob orig guard [] wl  in
                        solve env uu____12747
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12750,uu____12751) ->
                   let head1 =
                     let uu____12759 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12759
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____12790 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12790
                       FStar_Pervasives_Native.fst
                      in
                   let uu____12818 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12818
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12827 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12827
                      then
                        let guard =
                          let uu____12834 =
                            let uu____12835 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12835 = FStar_Syntax_Util.Equal  in
                          if uu____12834
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12838 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_72  ->
                                  FStar_Pervasives_Native.Some _0_72)
                               uu____12838)
                           in
                        let uu____12840 = solve_prob orig guard [] wl  in
                        solve env uu____12840
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12843,uu____12844) ->
                   let head1 =
                     let uu____12848 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12848
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____12879 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12879
                       FStar_Pervasives_Native.fst
                      in
                   let uu____12907 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12907
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12916 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12916
                      then
                        let guard =
                          let uu____12923 =
                            let uu____12924 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12924 = FStar_Syntax_Util.Equal  in
                          if uu____12923
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12927 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_73  ->
                                  FStar_Pervasives_Native.Some _0_73)
                               uu____12927)
                           in
                        let uu____12929 = solve_prob orig guard [] wl  in
                        solve env uu____12929
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____12932,uu____12933) ->
                   let head1 =
                     let uu____12937 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12937
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____12968 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12968
                       FStar_Pervasives_Native.fst
                      in
                   let uu____12996 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12996
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13005 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13005
                      then
                        let guard =
                          let uu____13012 =
                            let uu____13013 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13013 = FStar_Syntax_Util.Equal  in
                          if uu____13012
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13016 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_74  ->
                                  FStar_Pervasives_Native.Some _0_74)
                               uu____13016)
                           in
                        let uu____13018 = solve_prob orig guard [] wl  in
                        solve env uu____13018
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____13021,uu____13022) ->
                   let head1 =
                     let uu____13026 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13026
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____13057 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13057
                       FStar_Pervasives_Native.fst
                      in
                   let uu____13085 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13085
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13094 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13094
                      then
                        let guard =
                          let uu____13101 =
                            let uu____13102 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13102 = FStar_Syntax_Util.Equal  in
                          if uu____13101
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13105 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_75  ->
                                  FStar_Pervasives_Native.Some _0_75)
                               uu____13105)
                           in
                        let uu____13107 = solve_prob orig guard [] wl  in
                        solve env uu____13107
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____13110,uu____13111) ->
                   let head1 =
                     let uu____13124 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13124
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____13155 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13155
                       FStar_Pervasives_Native.fst
                      in
                   let uu____13183 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13183
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13192 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13192
                      then
                        let guard =
                          let uu____13199 =
                            let uu____13200 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13200 = FStar_Syntax_Util.Equal  in
                          if uu____13199
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13203 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____13203)
                           in
                        let uu____13205 = solve_prob orig guard [] wl  in
                        solve env uu____13205
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13208,FStar_Syntax_Syntax.Tm_match uu____13209) ->
                   let head1 =
                     let uu____13228 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13228
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____13259 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13259
                       FStar_Pervasives_Native.fst
                      in
                   let uu____13287 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13287
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13296 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13296
                      then
                        let guard =
                          let uu____13303 =
                            let uu____13304 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13304 = FStar_Syntax_Util.Equal  in
                          if uu____13303
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13307 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____13307)
                           in
                        let uu____13309 = solve_prob orig guard [] wl  in
                        solve env uu____13309
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13312,FStar_Syntax_Syntax.Tm_uinst uu____13313) ->
                   let head1 =
                     let uu____13321 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13321
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____13352 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13352
                       FStar_Pervasives_Native.fst
                      in
                   let uu____13380 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13380
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13389 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13389
                      then
                        let guard =
                          let uu____13396 =
                            let uu____13397 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13397 = FStar_Syntax_Util.Equal  in
                          if uu____13396
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13400 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____13400)
                           in
                        let uu____13402 = solve_prob orig guard [] wl  in
                        solve env uu____13402
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13405,FStar_Syntax_Syntax.Tm_name uu____13406) ->
                   let head1 =
                     let uu____13410 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13410
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____13441 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13441
                       FStar_Pervasives_Native.fst
                      in
                   let uu____13469 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13469
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13478 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13478
                      then
                        let guard =
                          let uu____13485 =
                            let uu____13486 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13486 = FStar_Syntax_Util.Equal  in
                          if uu____13485
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13489 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____13489)
                           in
                        let uu____13491 = solve_prob orig guard [] wl  in
                        solve env uu____13491
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13494,FStar_Syntax_Syntax.Tm_constant uu____13495) ->
                   let head1 =
                     let uu____13499 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13499
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____13530 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13530
                       FStar_Pervasives_Native.fst
                      in
                   let uu____13558 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13558
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13567 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13567
                      then
                        let guard =
                          let uu____13574 =
                            let uu____13575 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13575 = FStar_Syntax_Util.Equal  in
                          if uu____13574
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13578 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____13578)
                           in
                        let uu____13580 = solve_prob orig guard [] wl  in
                        solve env uu____13580
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13583,FStar_Syntax_Syntax.Tm_fvar uu____13584) ->
                   let head1 =
                     let uu____13588 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13588
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____13619 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13619
                       FStar_Pervasives_Native.fst
                      in
                   let uu____13647 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13647
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13656 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13656
                      then
                        let guard =
                          let uu____13663 =
                            let uu____13664 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13664 = FStar_Syntax_Util.Equal  in
                          if uu____13663
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13667 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____13667)
                           in
                        let uu____13669 = solve_prob orig guard [] wl  in
                        solve env uu____13669
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13672,FStar_Syntax_Syntax.Tm_app uu____13673) ->
                   let head1 =
                     let uu____13686 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13686
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____13717 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13717
                       FStar_Pervasives_Native.fst
                      in
                   let uu____13745 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13745
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13754 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13754
                      then
                        let guard =
                          let uu____13761 =
                            let uu____13762 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13762 = FStar_Syntax_Util.Equal  in
                          if uu____13761
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13765 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____13765)
                           in
                        let uu____13767 = solve_prob orig guard [] wl  in
                        solve env uu____13767
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let uu____13770,uu____13771) ->
                   let uu____13779 =
                     let uu____13780 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13781 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13780
                       uu____13781
                      in
                   failwith uu____13779
               | (FStar_Syntax_Syntax.Tm_delayed uu____13782,uu____13783) ->
                   let uu____13804 =
                     let uu____13805 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13806 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13805
                       uu____13806
                      in
                   failwith uu____13804
               | (uu____13807,FStar_Syntax_Syntax.Tm_delayed uu____13808) ->
                   let uu____13829 =
                     let uu____13830 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13831 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13830
                       uu____13831
                      in
                   failwith uu____13829
               | (uu____13832,FStar_Syntax_Syntax.Tm_let uu____13833) ->
                   let uu____13841 =
                     let uu____13842 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13843 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13842
                       uu____13843
                      in
                   failwith uu____13841
               | uu____13844 -> giveup env "head tag mismatch" orig)))

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
          mk_problem (p_scope orig) orig t1 rel t2
            FStar_Pervasives_Native.None reason
           in
        let solve_eq c1_comp c2_comp =
          (let uu____13876 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____13876
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____13884  ->
                  fun uu____13885  ->
                    match (uu____13884, uu____13885) with
                    | ((a1,uu____13895),(a2,uu____13897)) ->
                        let uu____13902 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg"
                           in
                        FStar_All.pipe_left
                          (fun _0_83  -> FStar_TypeChecker_Common.TProb _0_83)
                          uu____13902)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args
              in
           let guard =
             let uu____13908 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p)
                      FStar_Pervasives_Native.fst) sub_probs
                in
             FStar_Syntax_Util.mk_conj_l uu____13908  in
           let wl1 =
             solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl  in
           solve env (attempt sub_probs wl1))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____13928 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____13935)::[] -> wp1
              | uu____13948 ->
                  let uu____13954 =
                    let uu____13955 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name)
                       in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____13955
                     in
                  failwith uu____13954
               in
            let uu____13958 =
              let uu____13964 =
                let uu____13965 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____13965  in
              [uu____13964]  in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____13958;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____13966 = lift_c1 ()  in solve_eq uu____13966 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___132_13970  ->
                       match uu___132_13970 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____13971 -> false))
                in
             let uu____13972 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____13996)::uu____13997,(wp2,uu____13999)::uu____14000)
                   -> (wp1, wp2)
               | uu____14041 ->
                   let uu____14054 =
                     let uu____14055 =
                       let uu____14058 =
                         let uu____14059 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____14060 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____14059 uu____14060
                          in
                       (uu____14058, (env.FStar_TypeChecker_Env.range))  in
                     FStar_Errors.Error uu____14055  in
                   raise uu____14054
                in
             match uu____13972 with
             | (wpc1,wpc2) ->
                 let uu____14077 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____14077
                 then
                   let uu____14080 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____14080 wl
                 else
                   (let uu____14084 =
                      let uu____14088 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____14088  in
                    match uu____14084 with
                    | (c2_decl,qualifiers) ->
                        let uu____14100 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____14100
                        then
                          let c1_repr =
                            let uu____14103 =
                              let uu____14104 =
                                let uu____14105 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____14105  in
                              let uu____14106 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14104 uu____14106
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14103
                             in
                          let c2_repr =
                            let uu____14108 =
                              let uu____14109 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____14110 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14109 uu____14110
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14108
                             in
                          let prob =
                            let uu____14112 =
                              let uu____14115 =
                                let uu____14116 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____14117 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____14116
                                  uu____14117
                                 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____14115
                               in
                            FStar_TypeChecker_Common.TProb uu____14112  in
                          let wl1 =
                            let uu____14119 =
                              let uu____14121 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_Pervasives_Native.Some uu____14121  in
                            solve_prob orig uu____14119 [] wl  in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____14128 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____14128
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____14130 =
                                     let uu____14133 =
                                       let uu____14134 =
                                         let uu____14144 =
                                           let uu____14145 =
                                             let uu____14146 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ
                                                in
                                             [uu____14146]  in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____14145 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____14147 =
                                           let uu____14149 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____14150 =
                                             let uu____14152 =
                                               let uu____14153 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____14153
                                                in
                                             [uu____14152]  in
                                           uu____14149 :: uu____14150  in
                                         (uu____14144, uu____14147)  in
                                       FStar_Syntax_Syntax.Tm_app uu____14134
                                        in
                                     FStar_Syntax_Syntax.mk uu____14133  in
                                   uu____14130
                                     (FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____14164 =
                                    let uu____14167 =
                                      let uu____14168 =
                                        let uu____14178 =
                                          let uu____14179 =
                                            let uu____14180 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ
                                               in
                                            [uu____14180]  in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____14179 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____14181 =
                                          let uu____14183 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____14184 =
                                            let uu____14186 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____14187 =
                                              let uu____14189 =
                                                let uu____14190 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____14190
                                                 in
                                              [uu____14189]  in
                                            uu____14186 :: uu____14187  in
                                          uu____14183 :: uu____14184  in
                                        (uu____14178, uu____14181)  in
                                      FStar_Syntax_Syntax.Tm_app uu____14168
                                       in
                                    FStar_Syntax_Syntax.mk uu____14167  in
                                  uu____14164
                                    (FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r)
                              in
                           let base_prob =
                             let uu____14201 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type"
                                in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_TypeChecker_Common.TProb _0_84)
                               uu____14201
                              in
                           let wl1 =
                             let uu____14207 =
                               let uu____14209 =
                                 let uu____14212 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____14212 g  in
                               FStar_All.pipe_left
                                 (fun _0_85  ->
                                    FStar_Pervasives_Native.Some _0_85)
                                 uu____14209
                                in
                             solve_prob orig uu____14207 [] wl  in
                           solve env (attempt [base_prob] wl1))))
           in
        let uu____14222 = FStar_Util.physical_equality c1 c2  in
        if uu____14222
        then
          let uu____14223 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____14223
        else
          ((let uu____14226 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____14226
            then
              let uu____14227 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____14228 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____14227
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____14228
            else ());
           (let uu____14230 =
              let uu____14233 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____14234 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____14233, uu____14234)  in
            match uu____14230 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14238),FStar_Syntax_Syntax.Total
                    (t2,uu____14240)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____14253 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____14253 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14256,FStar_Syntax_Syntax.Total uu____14257) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14269),FStar_Syntax_Syntax.Total
                    (t2,uu____14271)) ->
                     let uu____14284 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____14284 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14288),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14290)) ->
                     let uu____14303 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____14303 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14307),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14309)) ->
                     let uu____14322 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____14322 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14325,FStar_Syntax_Syntax.Comp uu____14326) ->
                     let uu____14332 =
                       let uu___176_14335 = problem  in
                       let uu____14338 =
                         let uu____14339 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14339
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_14335.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14338;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_14335.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_14335.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_14335.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_14335.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_14335.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_14335.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_14335.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_14335.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____14332 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____14340,FStar_Syntax_Syntax.Comp uu____14341) ->
                     let uu____14347 =
                       let uu___176_14350 = problem  in
                       let uu____14353 =
                         let uu____14354 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14354
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_14350.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14353;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_14350.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_14350.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_14350.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_14350.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_14350.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_14350.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_14350.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_14350.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____14347 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14355,FStar_Syntax_Syntax.GTotal uu____14356) ->
                     let uu____14362 =
                       let uu___177_14365 = problem  in
                       let uu____14368 =
                         let uu____14369 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14369
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14365.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_14365.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14365.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14368;
                         FStar_TypeChecker_Common.element =
                           (uu___177_14365.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14365.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14365.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14365.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14365.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14365.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____14362 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14370,FStar_Syntax_Syntax.Total uu____14371) ->
                     let uu____14377 =
                       let uu___177_14380 = problem  in
                       let uu____14383 =
                         let uu____14384 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14384
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14380.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_14380.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14380.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14383;
                         FStar_TypeChecker_Common.element =
                           (uu___177_14380.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14380.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14380.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14380.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14380.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14380.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____14377 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14385,FStar_Syntax_Syntax.Comp uu____14386) ->
                     let uu____14387 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21)))
                        in
                     if uu____14387
                     then
                       let uu____14388 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____14388 wl
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
                           (let uu____14398 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____14398
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____14400 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____14400 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____14402 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____14403 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ
                                        in
                                     FStar_Syntax_Util.non_informative
                                       uu____14403)
                                   in
                                if uu____14402
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
                                  (let uu____14406 =
                                     let uu____14407 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name
                                        in
                                     let uu____14408 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name
                                        in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____14407 uu____14408
                                      in
                                   giveup env uu____14406 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____14413 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____14433  ->
              match uu____14433 with
              | (uu____14444,uu____14445,u,uu____14447,uu____14448,uu____14449)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____14413 (FStar_String.concat ", ")
  
let ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____14478 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____14478 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____14488 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____14500  ->
                match uu____14500 with
                | (u1,u2) ->
                    let uu____14505 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____14506 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____14505 uu____14506))
         in
      FStar_All.pipe_right uu____14488 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____14518,[])) -> "{}"
      | uu____14531 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____14541 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____14541
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____14544 =
              FStar_List.map
                (fun uu____14548  ->
                   match uu____14548 with
                   | (uu____14551,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____14544 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____14555 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____14555 imps
  
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14593 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel")
       in
    if uu____14593
    then
      let uu____14594 = FStar_TypeChecker_Normalize.term_to_string env lhs
         in
      let uu____14595 = FStar_TypeChecker_Normalize.term_to_string env rhs
         in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14594
        (rel_to_string rel) uu____14595
    else "TOP"  in
  let p = new_problem env lhs rel rhs elt loc reason  in p 
let new_t_prob :
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
            let uu____14615 =
              let uu____14617 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left
                (fun _0_86  -> FStar_Pervasives_Native.Some _0_86)
                uu____14617
               in
            FStar_Syntax_Syntax.new_bv uu____14615 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____14623 =
              let uu____14625 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left
                (fun _0_87  -> FStar_Pervasives_Native.Some _0_87)
                uu____14625
               in
            let uu____14627 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____14623 uu____14627  in
          ((FStar_TypeChecker_Common.TProb p), x)
  
let solve_and_commit :
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
          let uu____14650 = FStar_Options.eager_inference ()  in
          if uu____14650
          then
            let uu___178_14651 = probs  in
            {
              attempting = (uu___178_14651.attempting);
              wl_deferred = (uu___178_14651.wl_deferred);
              ctr = (uu___178_14651.ctr);
              defer_ok = false;
              smt_ok = (uu___178_14651.smt_ok);
              tcenv = (uu___178_14651.tcenv)
            }
          else probs  in
        let tx = FStar_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred ->
            (FStar_Unionfind.commit tx; FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            (FStar_Unionfind.rollback tx;
             (let uu____14662 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____14662
              then
                let uu____14663 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____14663
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
          ((let uu____14673 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____14673
            then
              let uu____14674 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14674
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f
               in
            (let uu____14678 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____14678
             then
               let uu____14679 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14679
             else ());
            (let f2 =
               let uu____14682 =
                 let uu____14683 = FStar_Syntax_Util.unmeta f1  in
                 uu____14683.FStar_Syntax_Syntax.n  in
               match uu____14682 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14687 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___179_14688 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___179_14688.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___179_14688.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___179_14688.FStar_TypeChecker_Env.implicits)
             })))
  
let with_guard :
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
            let uu____14703 =
              let uu____14704 =
                let uu____14705 =
                  let uu____14706 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____14706
                    (fun _0_88  -> FStar_TypeChecker_Common.NonTrivial _0_88)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14705;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____14704  in
            FStar_All.pipe_left
              (fun _0_89  -> FStar_Pervasives_Native.Some _0_89) uu____14703
  
let with_guard_no_simp env prob dopt =
  match dopt with
  | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some d ->
      let uu____14739 =
        let uu____14740 =
          let uu____14741 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst
             in
          FStar_All.pipe_right uu____14741
            (fun _0_90  -> FStar_TypeChecker_Common.NonTrivial _0_90)
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____14740;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        }  in
      FStar_Pervasives_Native.Some uu____14739
  
let try_teq :
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
          (let uu____14767 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____14767
           then
             let uu____14768 = FStar_Syntax_Print.term_to_string t1  in
             let uu____14769 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14768
               uu____14769
           else ());
          (let prob =
             let uu____14772 =
               let uu____14775 = FStar_TypeChecker_Env.get_range env  in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____14775
                in
             FStar_All.pipe_left
               (fun _0_91  -> FStar_TypeChecker_Common.TProb _0_91)
               uu____14772
              in
           let g =
             let uu____14780 =
               let uu____14782 = singleton' env prob smt_ok  in
               solve_and_commit env uu____14782
                 (fun uu____14783  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob) uu____14780  in
           g)
  
let teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14797 = try_teq true env t1 t2  in
        match uu____14797 with
        | FStar_Pervasives_Native.None  ->
            let uu____14799 =
              let uu____14800 =
                let uu____14803 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1
                   in
                let uu____14804 = FStar_TypeChecker_Env.get_range env  in
                (uu____14803, uu____14804)  in
              FStar_Errors.Error uu____14800  in
            raise uu____14799
        | FStar_Pervasives_Native.Some g ->
            ((let uu____14807 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____14807
              then
                let uu____14808 = FStar_Syntax_Print.term_to_string t1  in
                let uu____14809 = FStar_Syntax_Print.term_to_string t2  in
                let uu____14810 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____14808
                  uu____14809 uu____14810
              else ());
             g)
  
let try_subtype' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        Prims.bool ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        fun smt_ok  ->
          (let uu____14826 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____14826
           then
             let uu____14827 =
               FStar_TypeChecker_Normalize.term_to_string env t1  in
             let uu____14828 =
               FStar_TypeChecker_Normalize.term_to_string env t2  in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____14827
               uu____14828
           else ());
          (let uu____14830 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2  in
           match uu____14830 with
           | (prob,x) ->
               let g =
                 let uu____14838 =
                   let uu____14840 = singleton' env prob smt_ok  in
                   solve_and_commit env uu____14840
                     (fun uu____14841  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____14838  in
               ((let uu____14847 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g)
                    in
                 if uu____14847
                 then
                   let uu____14848 =
                     FStar_TypeChecker_Normalize.term_to_string env t1  in
                   let uu____14849 =
                     FStar_TypeChecker_Normalize.term_to_string env t2  in
                   let uu____14850 =
                     let uu____14851 = FStar_Util.must g  in
                     guard_to_string env uu____14851  in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____14848 uu____14849 uu____14850
                 else ());
                abstract_guard x g))
  
let try_subtype :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
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
          let uu____14875 = FStar_TypeChecker_Env.get_range env  in
          let uu____14876 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.err uu____14875 uu____14876
  
let sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____14888 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____14888
         then
           let uu____14889 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____14890 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____14889
             uu____14890
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB  in
         let prob =
           let uu____14895 =
             let uu____14898 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____14898 "sub_comp"
              in
           FStar_All.pipe_left
             (fun _0_92  -> FStar_TypeChecker_Common.CProb _0_92) uu____14895
            in
         let uu____14901 =
           let uu____14903 = singleton env prob  in
           solve_and_commit env uu____14903
             (fun uu____14904  -> FStar_Pervasives_Native.None)
            in
         FStar_All.pipe_left (with_guard env prob) uu____14901)
  
let solve_universe_inequalities' :
  FStar_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                                 FStar_Syntax_Syntax.universe)
                                                 FStar_Pervasives_Native.tuple2
                                                 Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____14923  ->
        match uu____14923 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Unionfind.rollback tx;
              (let uu____14948 =
                 let uu____14949 =
                   let uu____14952 =
                     let uu____14953 = FStar_Syntax_Print.univ_to_string u1
                        in
                     let uu____14954 = FStar_Syntax_Print.univ_to_string u2
                        in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____14953 uu____14954
                      in
                   let uu____14955 = FStar_TypeChecker_Env.get_range env  in
                   (uu____14952, uu____14955)  in
                 FStar_Errors.Error uu____14949  in
               raise uu____14948)
               in
            let equiv v1 v' =
              let uu____14963 =
                let uu____14966 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____14967 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____14966, uu____14967)  in
              match uu____14963 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Unionfind.equivalent v0 v0'
              | uu____14975 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____14989 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____14989 with
                      | FStar_Syntax_Syntax.U_unif uu____14993 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____15004  ->
                                    match uu____15004 with
                                    | (u,v') ->
                                        let uu____15010 = equiv v1 v'  in
                                        if uu____15010
                                        then
                                          let uu____15012 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u))
                                             in
                                          (if uu____15012 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____15022 -> []))
               in
            let uu____15025 =
              let wl =
                let uu___180_15028 = empty_worklist env  in
                {
                  attempting = (uu___180_15028.attempting);
                  wl_deferred = (uu___180_15028.wl_deferred);
                  ctr = (uu___180_15028.ctr);
                  defer_ok = false;
                  smt_ok = (uu___180_15028.smt_ok);
                  tcenv = (uu___180_15028.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____15035  ->
                      match uu____15035 with
                      | (lb,v1) ->
                          let uu____15040 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____15040 with
                           | USolved wl1 -> ()
                           | uu____15042 -> fail lb v1)))
               in
            let rec check_ineq uu____15048 =
              match uu____15048 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____15055) -> true
                   | (FStar_Syntax_Syntax.U_succ
                      u0,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name
                      u0,FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif
                      u0,FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Unionfind.equivalent u0 v0
                   | (FStar_Syntax_Syntax.U_name
                      uu____15067,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____15069,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____15074) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____15078,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____15083 -> false)
               in
            let uu____15086 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____15092  ->
                      match uu____15092 with
                      | (u,v1) ->
                          let uu____15097 = check_ineq (u, v1)  in
                          if uu____15097
                          then true
                          else
                            ((let uu____15100 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____15100
                              then
                                let uu____15101 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____15102 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____15101
                                  uu____15102
                              else ());
                             false)))
               in
            if uu____15086
            then ()
            else
              ((let uu____15106 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____15106
                then
                  ((let uu____15108 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____15108);
                   FStar_Unionfind.rollback tx;
                   (let uu____15114 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____15114))
                else ());
               (let uu____15120 =
                  let uu____15121 =
                    let uu____15124 = FStar_TypeChecker_Env.get_range env  in
                    ("Failed to solve universe inequalities for inductives",
                      uu____15124)
                     in
                  FStar_Errors.Error uu____15121  in
                raise uu____15120))
  
let solve_universe_inequalities :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                               FStar_Syntax_Syntax.universe)
                                               FStar_Pervasives_Native.tuple2
                                               Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.unit
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
      let fail uu____15157 =
        match uu____15157 with
        | (d,s) ->
            let msg = explain env d s  in
            raise (FStar_Errors.Error (msg, (p_loc d)))
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____15167 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____15167
       then
         let uu____15168 = wl_to_string wl  in
         let uu____15169 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits)
            in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____15168 uu____15169
       else ());
      (let g1 =
         let uu____15181 = solve_and_commit env wl fail  in
         match uu____15181 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___181_15188 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___181_15188.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___181_15188.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___181_15188.FStar_TypeChecker_Env.implicits)
             }
         | uu____15191 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___182_15194 = g1  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___182_15194.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___182_15194.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___182_15194.FStar_TypeChecker_Env.implicits)
        }))
  
let discharge_guard' :
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
          let g1 = solve_deferred_constraints env g  in
          let ret_g =
            let uu___183_15220 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___183_15220.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___183_15220.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___183_15220.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____15221 =
            let uu____15222 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____15222  in
          if uu____15221
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____15228 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery"))
                      in
                   if uu____15228
                   then
                     let uu____15229 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____15230 =
                       let uu____15231 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____15231
                        in
                     FStar_Errors.diag uu____15229 uu____15230
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Simplify] env vc
                      in
                   match check_trivial vc1 with
                   | FStar_TypeChecker_Common.Trivial  ->
                       FStar_Pervasives_Native.Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then FStar_Pervasives_Native.None
                       else
                         ((let uu____15240 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____15240
                           then
                             let uu____15241 =
                               FStar_TypeChecker_Env.get_range env  in
                             let uu____15242 =
                               let uu____15243 =
                                 FStar_Syntax_Print.term_to_string vc2  in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____15243
                                in
                             FStar_Errors.diag uu____15241 uu____15242
                           else ());
                          (let vcs =
                             let uu____15249 = FStar_Options.use_tactics ()
                                in
                             if uu____15249
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)]  in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____15263  ->
                                   match uu____15263 with
                                   | (env1,goal) ->
                                       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                         use_env_range_msg env1 goal)));
                          FStar_Pervasives_Native.Some ret_g))))
  
let discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15274 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____15274 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____15279 =
            let uu____15280 =
              let uu____15283 = FStar_TypeChecker_Env.get_range env  in
              ("Expected a trivial pre-condition", uu____15283)  in
            FStar_Errors.Error uu____15280  in
          raise uu____15279
  
let discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15290 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____15290 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let resolve_implicits :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____15310 = FStar_Unionfind.find u  in
      match uu____15310 with
      | FStar_Syntax_Syntax.Uvar  -> true
      | uu____15319 -> false  in
    let rec until_fixpoint acc implicits =
      let uu____15334 = acc  in
      match uu____15334 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____15380 = hd1  in
               (match uu____15380 with
                | (uu____15387,env,u,tm,k,r) ->
                    let uu____15393 = unresolved u  in
                    if uu____15393
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k  in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm
                          in
                       (let uu____15411 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck")
                           in
                        if uu____15411
                        then
                          let uu____15412 =
                            FStar_Syntax_Print.uvar_to_string u  in
                          let uu____15416 =
                            FStar_Syntax_Print.term_to_string tm1  in
                          let uu____15417 =
                            FStar_Syntax_Print.term_to_string k  in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____15412 uu____15416 uu____15417
                        else ());
                       (let uu____15419 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___184_15423 = env1  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___184_15423.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___184_15423.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___184_15423.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___184_15423.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___184_15423.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___184_15423.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___184_15423.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___184_15423.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___184_15423.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___184_15423.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___184_15423.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___184_15423.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___184_15423.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___184_15423.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___184_15423.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___184_15423.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___184_15423.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___184_15423.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___184_15423.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___184_15423.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___184_15423.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___184_15423.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___184_15423.FStar_TypeChecker_Env.qname_and_index)
                             }) tm1
                           in
                        match uu____15419 with
                        | (uu____15424,uu____15425,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___185_15428 = g1  in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___185_15428.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___185_15428.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___185_15428.FStar_TypeChecker_Env.implicits)
                                }
                              else g1  in
                            let g' =
                              let uu____15431 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____15435  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true
                                 in
                              match uu____15431 with
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
    let uu___186_15450 = g  in
    let uu____15451 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___186_15450.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___186_15450.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___186_15450.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____15451
    }
  
let force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____15479 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____15479 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____15486 = discharge_guard env g1  in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____15486
      | (reason,uu____15488,uu____15489,e,t,r)::uu____15493 ->
          let uu____15507 =
            let uu____15508 = FStar_Syntax_Print.term_to_string t  in
            let uu____15509 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2
              "Failed to resolve implicit argument of type '%s' introduced in %s"
              uu____15508 uu____15509
             in
          FStar_Errors.err r uu____15507
  
let universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___187_15516 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___187_15516.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___187_15516.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___187_15516.FStar_TypeChecker_Env.implicits)
      }
  
let teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15534 = try_teq false env t1 t2  in
        match uu____15534 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g ->
            let uu____15537 =
              discharge_guard' FStar_Pervasives_Native.None env g false  in
            (match uu____15537 with
             | FStar_Pervasives_Native.Some uu____15541 -> true
             | FStar_Pervasives_Native.None  -> false)
  